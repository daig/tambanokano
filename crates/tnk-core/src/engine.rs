//! The [`Engine`] — the instantiable owner of all runtime state (decision **D1**: no globals,
//! so several engines can coexist, e.g. for meta-interpreters).
//!
//! Internally it is split (Stage A4 / review R3 H1) into an immutable-during-reduction `Signature`
//! (sorts, symbols, compiled equations) and a mutable `Runtime` (the GC'd DAG arena, roots, and
//! rewrite statistics): matching and instantiation hold a *shared* borrow of the signature while
//! mutating the runtime, so a rewrite instantiates an equation's right-hand side straight out of
//! the still-borrowed equation table — no defensive clone. [`Engine`] is a thin facade that
//! re-exposes the same public API over the two halves.
//!
//! It computes each node's least sort at construction and runs garbage collection (decision **D2**:
//! non-moving mark-sweep) over the DAG from an explicit root set.

use crate::arena::Arena;
use crate::dag::{DagId, DagNode, NaValue, NodeTerm};
use crate::num::Nat;
use crate::rewrite::Rewriting;
use crate::root::{RootGuard, Roots};
use crate::search::{Arrow, Search};
use crate::sort::{SortId, Sorts};
use crate::symbol::{Axioms, OpDeclaration, SpecialOp, Symbol, SymbolId, Theory};
use crate::term::{ConditionFragment, Equation, Membership, Subst, Term};
use crate::theory::{LhsAutomaton, Subproblem};
use std::cmp::Ordering;
use std::collections::{HashMap, HashSet, VecDeque};

/// An equation as stored in the engine: its left-hand side compiled to a theory [`LhsAutomaton`]
/// (decision D3 / review R3 C1), with the right-hand side and variable count kept for instantiation.
/// The public [`Equation`] (lhs as a [`Term`]) is compiled into this by [`Engine::add_equation`].
struct CompiledEquation {
    /// Dense per-module id (assigned by [`Signature::push_equation`]); the frontend keeps this
    /// equation's source `Term`s + variable names at `eq_traces[id]` for the trace renderer.
    id: u32,
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    /// Condition fragments (empty for an unconditional `eq`); all must hold for the equation to apply,
    /// and a failed condition backtracks into the next matcher solution (B2.3).
    condition: Vec<CompiledFragment>,
    /// `[owise]`: this equation is tried only if no non-owise equation of the symbol applies (B2.3b).
    owise: bool,
    /// `true` iff [`rhs`](Self::rhs) contains a repeated compound subterm (C7): when set, the rhs is
    /// instantiated inside a dedup window so the duplicate becomes one shared node (Maude's `RhsBuilder`
    /// CSE), which `reduce` then normalizes once. `false` (the common case — e.g. `fib`'s `s(N + M)`,
    /// which shares nothing) takes the plain instantiate path with zero dedup overhead.
    rhs_shares: bool,
}

/// A membership axiom `mb lhs : sort` compiled for the engine: its lhs as a theory [`LhsAutomaton`]
/// plus the target sort and variable count. The public [`Membership`] is compiled into this by
/// [`Signature::add_membership`]. (Conditional `cmb` gains a condition in B2.3.)
struct SortConstraint {
    /// Dense per-module id (assigned by [`Signature::push_membership`]); the frontend keeps this
    /// membership's source `Term` + variable names at `mb_traces[id]` for the trace renderer.
    id: u32,
    lhs: LhsAutomaton,
    sort: SortId,
    nr_vars: u32,
    /// Condition fragments (empty for an unconditional `mb`); checked under the membership match's
    /// substitution before the sort is lowered (B2.3c `cmb`).
    condition: Vec<CompiledFragment>,
}

/// A rule `rl lhs => rhs` compiled for the engine: structurally a [`CompiledEquation`] minus `[owise]`
/// (rules have no owise phase). Unlike equations, rules live in their own [`Signature::rules`] table and
/// are applied **only** by `rewrite`/`frewrite`/`search` (Pillar A) — never by [`reduce`](Engine::reduce),
/// which consults only `equations`. The frontend keeps this rule's source `Term`s + variable names +
/// label at `rl_traces[id]` for the trace renderer and `show path` (`===[ rl ... ]===>`).
struct CompiledRule {
    id: u32,
    lhs: LhsAutomaton,
    rhs: Term,
    nr_vars: u32,
    /// Condition fragments (empty for an unconditional `rl`); a `crl` may additionally carry a **rewrite**
    /// fragment `t => p` (Pillar A-v) — the one fragment kind equations/memberships may not have.
    condition: Vec<CompiledFragment>,
    /// As [`CompiledEquation::rhs_shares`] — C7 dedup window for an rhs with a repeated compound subterm.
    rhs_shares: bool,
}

/// A condition fragment compiled for evaluation: like the public [`ConditionFragment`] but with the
/// matching fragment's pattern compiled to an [`LhsAutomaton`]. Built by
/// [`Signature::compile_condition`]. The `fresh_vars` of a matching fragment are unbound before each
/// match attempt so backtracking re-binds cleanly.
pub(crate) enum CompiledFragment {
    Equality { lhs: Term, rhs: Term },
    SortTest { term: Term, sort: SortId },
    Matching { pattern: LhsAutomaton, subject: Term, fresh_vars: Vec<u32> },
    /// `lhs => pattern` — a rewrite condition (rule-only, Pillar A-v): a nested `=>*` reachability search
    /// from `lhs`'s instance, matching `pattern` against each reachable state.
    Rewrite { lhs: Term, pattern: LhsAutomaton, fresh_vars: Vec<u32> },
}

/// Which statement a condition belongs to — gates the `=>` (rewrite) fragment, which is legal **only** in
/// a rule (`crl`) condition, never in an equation/membership (`ceq`/`cmb`).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum CondOwner {
    EqOrMb,
    Rule,
}

/// Whether [`Runtime::drive_match`]'s `accept` callback wants to stop at the first rewrite (equational
/// reduction and `rewrite`/`frewrite`, which take the first applicable statement) or keep enumerating
/// every solution (search successor collection, Pillar A-iv).
enum Flow {
    Stop,
    /// Keep enumerating every solution — used by the search successor-collector (Pillar A-iv); `rewrite`
    /// and equational reduction only ever return [`Flow::Stop`].
    #[allow(dead_code)]
    Continue,
}

/// Identifies the statement [`Runtime::drive_match`] is driving, for trace events and the F-2 condition
/// root set. `kind` selects the trace metadata (equation vs rule) and the [`RewriteKind`]; `frames`/`redex`
/// are threaded into [`condition_holds`](Runtime::condition_holds) for GC rooting of a conditional
/// statement's re-entrant condition reduction (moot for unconditional statements / GC-off REPL).
struct StmtCtx<'a> {
    kind: StmtKind,
    stmt_id: u32,
    frames: &'a [ReduceFrame],
    redex: DagId,
}

/// One position in the redex stack of [`Runtime::rewrite_step`]'s top-down traversal: the node, its
/// parent's index in the stack (`usize::MAX` for the root), and which flattened argument of the parent
/// it is — enough to rebuild the path to the root after a rewrite (Maude's `RedexPosition`).
struct RedexPos {
    node: DagId,
    parent: usize,
    arg_index: usize,
}

/// One pending node-normalization on the iterative [`Engine::reduce`] work-stack.
///
/// A frame mirrors one activation of the old recursive `reduce`/`reduce_args` pair: it reduces the
/// arguments selected by the operator's evaluation strategy (the standard one is every argument
/// left-to-right; `cursor` walks the strategy via [`Signature::strat_position`]), replacing each in
/// `args`, then drives the top-rewrite fixpoint by *reusing its own slot* for each rewritten term.
///
/// **A2 safe-point-GC contract** (the reason this is an explicit heap stack). The frames hold most
/// in-flight `DagId`s of an in-progress reduction — but *not all*: at the [`Engine::reduce`] loop
/// head a just-completed child sits only in the `child_result` local until it is delivered into its
/// parent's `args` on the next iteration. So the complete root set at the loop head is
/// `walk(stack) ∪ child_result`. GC must therefore be confined to the loop head:
/// `try_rewrite_top`/`instantiate`/`make_free` build fresh nodes whose ids live only in native-stack
/// locals (`instantiate`'s `arg_ids`, the `Subst` bindings, the `rebuilt` node mid-rewrite) and are
/// *not* discoverable by a stack walk, so they must not be safe points.
struct ReduceFrame {
    /// The node this frame was **first** pushed for — preserved across the Phase-2 rewrite-replace
    /// (which overwrites `original` with each successive redex). When the frame reaches a normal form,
    /// that form is recorded as `start`'s [`nf`](crate::dag::DagNode::nf) so a *shared* reference to
    /// `start` forwards to the result instead of re-reducing it (C7). For the initial frame `start ==
    /// original`; they diverge only once the node rewrites.
    start: DagId,
    /// The node this frame started from; returned unchanged when no child changed (preserves the
    /// shared DAG id rather than rebuilding an identical node).
    original: DagId,
    symbol: SymbolId,
    /// The original children of `original`, copied out so the spine can be walked across the `&mut
    /// self` reductions that may grow (and thus reallocate) the arena. The change test is `args != orig`.
    orig: Vec<DagId>,
    /// Current arguments: `orig` with each strategy-reduced position replaced by its normal form;
    /// positions the strategy leaves unreduced keep their `orig` value (lazy). The node is rebuilt from
    /// this.
    args: Vec<DagId>,
    /// Strategy steps taken so far — the cursor into the operator's strategy (or `0..arity` for the
    /// standard strategy); [`Signature::strat_position`] maps it to the argument position to reduce.
    cursor: usize,
}

/// The immutable-during-reduction half of the engine: the sort poset, the symbol table, and the
/// compiled equation set. Matching, instantiation, and reduction take this by shared reference, so
/// the [`Runtime`] can mutate the DAG arena while the equation table stays borrowed.
pub(crate) struct Signature {
    sorts: Sorts,
    symbols: Arena<Symbol>,
    /// Unconditional equations (LHS compiled to a theory automaton), indexed by lhs top symbol.
    equations: HashMap<SymbolId, Vec<CompiledEquation>>,
    /// Membership axioms (`mb`), indexed by lhs top symbol; applied to lower a node's least sort at
    /// construction (B2.2). Empty in modules without memberships — the construction hot path checks
    /// `memberships.is_empty()` before doing any per-node work, so the free reduce path is untouched.
    memberships: HashMap<SymbolId, Vec<SortConstraint>>,
    /// Rules (`rl`/`crl`), indexed by lhs top symbol. Applied **only** by `rewrite`/`frewrite`/`search`
    /// (Pillar A) — never by [`reduce`](Engine::reduce), so equational normal forms never apply a rule.
    /// Adding a rule does not bump `eq_epoch` (rules don't change any equational normal form).
    rules: HashMap<SymbolId, Vec<CompiledRule>>,
    /// Bumped whenever the equation set changes; stamped into nodes when they are proved canonical,
    /// so `add_equation` invalidates stale "reduced" results (review R2 H2). `0` is the "never
    /// reduced" sentinel stored on nodes, so this starts at `1`.
    eq_epoch: u32,
    /// Next dense equation id (the count of equations added). Assigned to each [`CompiledEquation`] so
    /// the frontend can key its trace metadata by it; per-module (each `Engine` starts at 0).
    next_eq_id: u32,
    /// Next dense membership-axiom id (the count of memberships added). Assigned to each
    /// [`SortConstraint`]; the trace counterpart of `next_eq_id`.
    next_mb_id: u32,
    /// Next dense rule id (the count of rules added). Assigned to each [`CompiledRule`]; the frontend
    /// keys its `rl_traces` metadata by it.
    next_rule_id: u32,
}

/// One recorded reduction event (opt-in via [`Engine::set_trace`]) — the structured stream the REPL
/// renders as Maude's full `trace`. Each event carries its **condition-nesting `depth`** (0 at the top
/// level, +1 inside every condition-fragment reduction): the REPL's `set trace condition off` renders
/// only depth-0 events, mirroring Maude's `CONDITION_EVAL` sub-context trace flag. Node ids held here
/// (redex/result/bindings/subject/whole) are rooted by [`safe_point_gc`](Runtime::safe_point_gc).
///
/// The `id`s name a module's compiled equations / membership axioms (dense, per-module, assigned by
/// [`Signature::push_equation`]/[`push_membership`](Signature::push_membership)); the frontend keeps the
/// source `Term`s + variable names keyed by them and renders the bodies.
#[derive(Debug, Clone)]
pub enum TraceEvent {
    /// A term rewrite: an equation (`eq_id = Some`) or a built-in (`special`) reduction (`eq_id =
    /// None`). `bindings[i]` is the matched value of the equation's variable `i` (`None` = unbound; empty
    /// for a built-in). `whole_before`/`whole_after` are the whole root term before/after this rewrite —
    /// `Some` only when whole-tracing is on (`set trace whole`); reconstructed from the reduce frame stack.
    Rewrite {
        kind: RewriteKind,
        eq_id: Option<u32>,
        depth: u32,
        redex: DagId,
        result: DagId,
        bindings: Vec<Option<DagId>>,
        whole_before: Option<DagId>,
        whole_after: Option<DagId>,
    },
    /// A membership-axiom sort narrowing (not a term rewrite): `subject`'s least sort was lowered from
    /// `old_sort` to `new_sort` by membership `mb_id`. `bindings` is the membership match's substitution.
    /// (`whole` is reserved for `set trace whole`; currently `None` — memberships fire at node
    /// construction, where the reduce frame stack isn't available, so the whole term isn't reconstructed.)
    Membership {
        mb_id: u32,
        depth: u32,
        subject: DagId,
        old_sort: SortId,
        new_sort: SortId,
        bindings: Vec<Option<DagId>>,
        whole: Option<DagId>,
    },
    /// Begin trying a conditional equation/membership against one matcher solution (a *trial*).
    /// `bindings` is the substitution so far (the lhs match; fresh `:=` variables are still `None`).
    TrialStart { kind: StmtKind, stmt_id: u32, depth: u32, bindings: Vec<Option<DagId>> },
    /// End a trial: `success` iff the whole condition held. `kind`/`depth` mirror the matching
    /// [`TrialStart`](TraceEvent::TrialStart) so the renderer gates (and so pairs) them identically.
    TrialEnd { kind: StmtKind, depth: u32, success: bool },
    /// Begin solving condition fragment `index` of `stmt_id`'s condition (`first_attempt = false` on a
    /// backtracking re-solve → Maude's `re-solving`).
    FragmentStart { kind: StmtKind, stmt_id: u32, index: u32, depth: u32, first_attempt: bool },
    /// End solving a condition fragment. On `success`, `bindings` is the substitution after the fragment
    /// (it may have bound fresh `:=` variables).
    FragmentEnd {
        kind: StmtKind,
        stmt_id: u32,
        index: u32,
        depth: u32,
        success: bool,
        bindings: Vec<Option<DagId>>,
    },
}

impl TraceEvent {
    /// The condition-nesting depth this event was recorded at (0 = top level). The REPL renders an
    /// event iff `depth == 0` or `set trace condition` is on.
    pub fn depth(&self) -> u32 {
        match self {
            TraceEvent::Rewrite { depth, .. }
            | TraceEvent::Membership { depth, .. }
            | TraceEvent::TrialStart { depth, .. }
            | TraceEvent::TrialEnd { depth, .. }
            | TraceEvent::FragmentStart { depth, .. }
            | TraceEvent::FragmentEnd { depth, .. } => *depth,
        }
    }

    /// Every DAG node id this event references (for GC rooting under in-reduction GC).
    fn for_each_id(&self, mut f: impl FnMut(DagId)) {
        let binds = |bs: &[Option<DagId>], f: &mut dyn FnMut(DagId)| bs.iter().flatten().for_each(|&d| f(d));
        match self {
            TraceEvent::Rewrite { redex, result, bindings, whole_before, whole_after, .. } => {
                f(*redex);
                f(*result);
                binds(bindings, &mut f);
                whole_before.iter().chain(whole_after.iter()).for_each(|&d| f(d));
            }
            TraceEvent::Membership { subject, bindings, whole, .. } => {
                f(*subject);
                binds(bindings, &mut f);
                whole.iter().for_each(|&d| f(d));
            }
            TraceEvent::TrialStart { bindings, .. } | TraceEvent::FragmentEnd { bindings, .. } => {
                binds(bindings, &mut f)
            }
            TraceEvent::TrialEnd { .. } | TraceEvent::FragmentStart { .. } => {}
        }
    }
}

/// What kind of rule produced a [`Rewrite`](TraceEvent::Rewrite) event.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RewriteKind {
    /// A user equation.
    Equation,
    /// A built-in (`special`) operator's reduction.
    BuiltIn,
    /// A user rule (`rl`/`crl`), applied by `rewrite`/`frewrite`/`search` (Pillar A).
    Rule,
}

/// Which statement table a trial / fragment / membership event refers to — selects the frontend
/// metadata (`eq_traces` vs `mb_traces`) the REPL looks `stmt_id` up in, and the `eqs`/`mbs` trace flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StmtKind {
    /// A (conditional) equation.
    Equation,
    /// A (conditional) membership axiom.
    Membership,
    /// A (conditional) rule (`rl`/`crl`) — selects the frontend `rl_traces` metadata and the `rls`
    /// trace flag (Pillar A).
    Rule,
}

/// The mutable half of the engine: the garbage-collected DAG arena, the GC root registry, and the
/// rewrite statistics. Operations that consult the signature (sorts/symbols/equations) take a
/// `&Signature`; everything else is pure arena work.
#[derive(Default)]
pub(crate) struct Runtime {
    dags: Arena<DagNode>,
    /// Count of equational rewrites applied (Maude's `rewrites` statistic). `pub(crate)` so the rewrite-
    /// path `counter` special ([`Runtime::try_counter`]) can count its step like a rule application.
    pub(crate) rewrite_count: u64,
    /// Next value for the `counter` built-in (Maude's `CounterSymbol`): each `rewrite`/`frewrite` step
    /// that fires a `counter` redex yields this and increments it. Reset to 0 at the start of each
    /// top-level rewriting command (not on `continue`). Inert under equational `reduce`.
    pub(crate) counter_value: u64,
    /// When `Some`, [`reduce`](Engine::reduce) records a structured [`TraceEvent`] stream here (opt-in
    /// via [`Engine::set_trace`]); `None` (the default) is zero-cost. Holds intermediate node ids, so it
    /// is rooted by [`safe_point_gc`](Self::safe_point_gc) — but it is meant for the REPL, which runs
    /// with in-reduction GC off.
    trace: Option<Vec<TraceEvent>>,
    /// Current condition-fragment nesting depth: 0 at top level, incremented around each condition
    /// fragment's re-entrant reduction (so events recorded inside a condition are tagged `depth >= 1`).
    /// Always maintained (a cheap `u32`), but only consulted when `trace` is `Some`.
    condition_depth: u32,
    /// Whether to reconstruct the whole root term at each rewrite (`set trace whole`). Off by default
    /// (the reconstruction allocates O(depth) nodes per rewrite, so it is gated). Only acts when tracing.
    record_whole: bool,
    /// Persistent GC roots held by live [`RootGuard`]s (decision D2 amendment). `gc` always marks
    /// from here; the shared `Rc<RefCell<…>>` lets a guard outlive a `&mut self` call.
    roots: Roots,
    /// If `Some(n)`, [`reduce`](Engine::reduce) collects at its loop head once this many DAG nodes
    /// have been allocated since the last collection — letting one large reduction run in bounded
    /// memory. `None` (default) disables in-reduction GC (callers collect between reductions).
    gc_interval: Option<u64>,
    /// DAG nodes allocated since the last collection (drives `gc_interval`).
    allocs_since_gc: u64,
    /// Engine-global GC roots that protect the **outer** reduction's working set across a re-entrant
    /// condition reduction (F-2). A condition fragment is evaluated by calling [`reduce`](Self::reduce)
    /// again; that nested reduce's [`safe_point_gc`](Self::safe_point_gc) can only see *its own* frame
    /// stack, so [`condition_holds`](Self::condition_holds) pushes the outer frames' roots + match
    /// bindings + redex here for the duration of the solve (Maude marks from all active rewriting
    /// contexts). `safe_point_gc` marks everything here in addition to the current stack. Used only when
    /// `gc_interval` is `Some` (otherwise GC never fires, so the vec stays empty — no overhead off-path).
    protected: Vec<DagId>,
    /// Construction-time structural-dedup memo (C7 Half 1), `None` (the default) except inside a
    /// [`begin_dedup`](Self::begin_dedup)…[`end_dedup`](Self::end_dedup) window. While `Some`, every
    /// [`alloc_node`](Self::alloc_node) returns an existing structurally-identical node instead of a
    /// duplicate, so a repeated subterm in the subject (or a sharing rhs) becomes **one** shared node —
    /// which `nf`-forwarding then reduces once. Construction-scoped (never spans a GC safe point), so the
    /// memo never holds a stale id; the default `None` path is a single `is_some()` branch on the
    /// allocation funnel, leaving the reduce hot path untouched. Bottom-up construction keeps the
    /// [`NodeTerm`] key shallow (children are deduped first, so identical subtrees already share ids).
    dedup: Option<HashMap<NodeTerm, DagId>>,
}

#[derive(Default)]
pub struct Engine {
    sig: Signature,
    rt: Runtime,
}

impl Default for Signature {
    fn default() -> Self {
        Signature {
            sorts: Sorts::default(),
            symbols: Arena::default(),
            equations: HashMap::default(),
            memberships: HashMap::default(),
            rules: HashMap::default(),
            eq_epoch: 1, // 0 is the "never reduced" sentinel stored on nodes
            next_eq_id: 0,
            next_mb_id: 0,
            next_rule_id: 0,
        }
    }
}

/// Whether `t` has a repeated **compound** subterm — some `Op` term appearing (by structural value) at
/// two or more positions. Decides an equation's `rhs_shares` flag (C7 Half 1): only such an rhs needs the
/// dedup window, so the common non-sharing rhs (e.g. `fib`'s `s(N + M)`) keeps the plain instantiate path.
/// Bare `Var`s are skipped — a repeated variable already shares through the substitution (`instantiate`
/// returns the one binding), so it is not a construction duplicate. Over-approximating is safe: a false
/// positive only enables the (idempotent) dedup window; there are no false negatives.
fn term_has_repeated_subterm(t: &Term) -> bool {
    let mut seen: HashSet<&Term> = HashSet::new();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        if let Term::Op { args, .. } = cur {
            if !seen.insert(cur) {
                return true; // this compound subterm was already seen elsewhere — a real duplicate
            }
            stack.extend(args.iter());
        }
    }
    false
}

// ======================================================================================
// Signature: sorts, symbols, equations (immutable during a reduction)
// ======================================================================================

impl Signature {
    pub(crate) fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sorts.add_sort(name)
    }
    pub(crate) fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sorts.add_subsort(sub, sup);
    }
    pub(crate) fn close_sorts(&mut self) {
        self.sorts.close();
    }
    pub(crate) fn sorts(&self) -> &Sorts {
        &self.sorts
    }

    pub(crate) fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms::default(),
            identity: None,
            strategy: None,
            frozen: None,
            special: None,
        })
    }

    /// Register an **ACU** operator (`assoc comm`, optionally with a two-sided `id:`). The operator
    /// must be binary (Maude requires associative operators to be binary); its arguments are stored
    /// flattened as a multiset and matched modulo AC(+U). `identity` is the constant symbol declared
    /// as `id: <const>`, or `None`.
    pub(crate) fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc comm` operator must be binary");
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: true, comm: true, idem: false, iter: false },
            identity,
            strategy: None,
            frozen: None,
            special: None,
        });
        self.commutative_sort_completion(id); // an asymmetric initial decl needs its swap
        id
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; its arguments are stored as a flattened ordered sequence and matched modulo
    /// associativity (with extension).
    pub(crate) fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "an `assoc` operator must be binary");
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: true, comm: false, idem: false, iter: false },
            identity,
            strategy: None,
            frozen: None,
            special: None,
        })
    }

    /// Register a **CUI** operator (`comm`, not associative, optionally `idem` and/or `id:`). Must be
    /// binary; its two arguments are stored in canonical order and matched modulo commutativity
    /// (idempotence and identity collapse `f(a,a)`/`f(a,e)` to a single element at construction).
    pub(crate) fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        assert_eq!(domain.len(), 2, "a `comm` operator must be binary");
        let id = self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { assoc: false, comm: true, idem, iter: false },
            identity,
            strategy: None,
            frozen: None,
            special: None,
        });
        self.commutative_sort_completion(id); // an asymmetric initial decl needs its swap
        id
    }

    /// Register an **S** (`iter`) operator: a unary stacked successor `s_` (Maude's `[iter]`). Its nodes
    /// store the iteration count compactly as `s^count(arg)` and match modulo the successor extension.
    /// Must be unary; not commutative, so no declaration completion.
    pub(crate) fn add_op_iter(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        assert_eq!(domain.len(), 1, "an `iter` operator must be unary");
        self.symbols.alloc(Symbol {
            name: name.into(),
            decls: vec![OpDeclaration { domain, range, ctor: false }],
            axioms: Axioms { iter: true, ..Default::default() },
            identity: None,
            strategy: None,
            frozen: None,
            special: None,
        })
    }
    pub(crate) fn symbol(&self, id: SymbolId) -> &Symbol {
        self.symbols.get(id)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading). All
    /// declarations of an operator must agree on arity; least-sort resolution walks them in the order
    /// added, so the *original* `add_op*` declaration stays first (the tie-break favours it). Must be
    /// called before any node of `sym` is built (sorts are cached at construction). The parser (B4) is
    /// the eventual real source; this is the hand-built-module entry point.
    pub(crate) fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        {
            let s = self.symbols.get_mut(sym);
            assert_eq!(
                s.decls[0].domain.len(),
                domain.len(),
                "overloaded declarations of `{}` must agree on arity",
                s.name()
            );
            s.decls.push(OpDeclaration { domain, range, ctor: false });
        }
        // Keep a commutative operator's declaration set complete under argument swap (no-op for free
        // and AU operators, whose declarations stay positional).
        self.commutative_sort_completion(sym);
    }

    /// Maude's `BinarySymbol::commutativeSortCompletion` (`Interface/binarySymbol.cc`): a commutative
    /// operator's declaration set is completed so that every **asymmetric** declaration `[a, b] -> r`
    /// also carries its swapped form `[b, a] -> r` (same range, same `ctor`), unless one is already
    /// present.
    ///
    /// Maude builds a *positional* sort diagram from the declarations and folds it left-to-right over
    /// an ACU multiset / CUI pair (`ACU_DagNode::argVecComputeBaseSort` → `computeMultSortIndex`);
    /// [`compute_sort`](Self::compute_sort) likewise checks `arg_sorts[i] <= decl.domain[i]`
    /// **positionally**. Commutativity requires either argument order to yield the same least sort,
    /// but the canonical element order (by [`dag_compare`](Runtime::dag_compare)) can present the
    /// lower-sorted element first — so without the swapped declaration an asymmetric overload such as
    /// NAT's `_+_ : NzNat Nat -> NzNat` would compute an argument-order-dependent (wrong) least sort
    /// (e.g. `z + nz : Nat` instead of `NzNat`). Completing the set restores order-independence
    /// without changing the fold. Idempotent (a swap's swap is the original, already present), so it is
    /// safe to run after each declaration is registered. AU (associative, non-commutative) and free
    /// operators are left untouched — their argument order is significant.
    fn commutative_sort_completion(&mut self, sym: SymbolId) {
        let s = self.symbols.get(sym);
        if !matches!(s.theory(), Theory::Acu | Theory::Cui) {
            return; // only commutative theories complete; AU / free stay positional
        }
        // Snapshot the current declarations so the shared borrow ends before the mutable push below
        // (the sort ids are `Copy`, so this clone is cheap and small).
        let decls: Vec<OpDeclaration> = s.decls.clone();
        let mut to_add: Vec<OpDeclaration> = Vec::new();
        for d in &decls {
            if d.domain.len() != 2 || d.domain[0] == d.domain[1] {
                continue; // a symmetric (or non-binary) declaration is its own swap
            }
            let swapped = vec![d.domain[1], d.domain[0]];
            let present = decls
                .iter()
                .chain(to_add.iter())
                .any(|e| e.domain == swapped && e.range == d.range && e.ctor == d.ctor);
            if !present {
                to_add.push(OpDeclaration { domain: swapped, range: d.range, ctor: d.ctor });
            }
        }
        self.symbols.get_mut(sym).decls.extend(to_add);
    }

    /// Mark every declaration of `sym` as a constructor (`[ctor]`, B2.4). Metadata only — it does not
    /// change reduction; recorded for the later constructor analysis.
    pub(crate) fn set_ctor(&mut self, sym: SymbolId) {
        for decl in &mut self.symbols.get_mut(sym).decls {
            decl.ctor = true;
        }
    }

    /// Set an evaluation strategy `strat (raw…)` on `sym` (B2.4). `raw` is the user sequence of 1-based
    /// argument positions ending in a single trailing `0` (reduce at top) — e.g. `[1, 0]` for a lazy
    /// `if_then_else_fi`. Stored as the 0-based positions to reduce, in order; arguments not listed are
    /// left unreduced. The general strategy (interleaved or absent `0`) is a follow-up — loud-assert.
    pub(crate) fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        let arity = self.symbols.get(sym).arity();
        assert_eq!(
            raw.last(),
            Some(&0),
            "evaluation strategy {raw:?} for `{}` must end in a single trailing 0 (reduce at top); \
             interleaved or absent top rewrites are a B-follow-up",
            self.symbols.get(sym).name()
        );
        let positions = &raw[..raw.len() - 1];
        assert!(
            positions.iter().all(|&p| p >= 1 && p as usize <= arity),
            "evaluation strategy {raw:?} for `{}` references an argument outside 1..={arity} (or has a \
             non-trailing 0)",
            self.symbols.get(sym).name()
        );
        self.symbols.get_mut(sym).strategy = Some(positions.iter().map(|&p| p - 1).collect());
    }

    /// Mark the frozen arguments of `sym` (`frozen` / `frozen (…)`, Pillar A). `raw` is the 1-based
    /// positions from the source — empty for a bare `[frozen]` (all arguments); stored 0-based.
    pub(crate) fn set_frozen(&mut self, sym: SymbolId, raw: &[u32]) {
        let arity = self.symbols.get(sym).arity();
        assert!(
            raw.iter().all(|&p| p >= 1 && p as usize <= arity),
            "frozen positions {raw:?} for `{}` reference an argument outside 1..={arity}",
            self.symbols.get(sym).name()
        );
        self.symbols.get_mut(sym).frozen = Some(raw.iter().map(|&p| p - 1).collect());
    }

    /// Attach a built-in reduction rule (`special (id-hook …)`, B3) to `sym`. The op-hook/term-hook
    /// references are passed already resolved to [`SymbolId`]s (the future parser does the resolution;
    /// for now the hand-built module supplies them). A [`SpecialOp::Branch`] is intrinsically lazy, so
    /// this installs its `strat (1 0)` (condition eager, branches lazy) — the real `if_then_else_fi`
    /// carries no user `strat`, so the seam wires it here (cf. the B2.4 lazy-strat mechanism).
    pub(crate) fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        if let SpecialOp::Branch { .. } = op {
            assert!(
                self.symbols.get(sym).strategy.is_none(),
                "`{}` is a Branch operator; its laziness is installed by the seam — it must not also \
                 carry a user strat",
                self.symbols.get(sym).name()
            );
            self.set_strategy(sym, &[1, 0]); // reduce the condition (arg 1) only, then the top rewrite
        }
        self.symbols.get_mut(sym).special = Some(op);
    }

    /// The argument position to reduce at strategy step `cursor` for `symbol` (B2.4), or `None` once the
    /// strategy is exhausted (→ attempt the top rewrite). The standard strategy reduces every argument
    /// left-to-right; a custom strategy reduces only its listed positions, in order.
    pub(crate) fn strat_position(&self, symbol: SymbolId, cursor: usize, arity: usize) -> Option<usize> {
        match &self.symbols.get(symbol).strategy {
            None => (cursor < arity).then_some(cursor),
            Some(positions) => positions.get(cursor).map(|&p| p as usize),
        }
    }

    /// Least sort of `symbol(args…)` whose arguments have sorts `arg_sorts`, under multi-declaration
    /// overloading — Maude's `findMinSortIndex` (sortTable.cc:369). The least sort is the minimum of
    /// the *applicable* declarations' range sorts (a declaration is applicable iff every `arg_sorts[i]
    /// <= decl.domain[i]`), breaking incomparable (non-preregular) ties toward the **earliest**
    /// declaration. Reproduced directly by intersecting range **down-sets** in declaration order
    /// (correctness-first; the flattened sort-diagram decision table is a later perf step). No
    /// applicable declaration → the error sort of the range's kind.
    pub(crate) fn compute_sort(&self, symbol: SymbolId, arg_sorts: &[SortId]) -> SortId {
        self.compute_sort_uniq(symbol, arg_sorts).0
    }

    /// The sort of a built-in **NA** constant — *value-dependent* (Maude's per-symbol NA sort
    /// functions), not just the least declared range: a length-1 string is `Char` else `String`; a
    /// finite float is `FiniteFloat` else `Float`; a quoted identifier is `Qid`. Concretely: among the
    /// symbol's declared range sorts, the most specific (min) when the value is "special" (a one-char
    /// string / a finite float), else the most general (max). A single-decl NA symbol (`Qid`) has
    /// min == max, so the value does not matter.
    pub(crate) fn compute_na_sort(&self, symbol: SymbolId, value: &NaValue) -> SortId {
        let decls = self.symbols.get(symbol).decls();
        let (mut min, mut max) = (decls[0].range, decls[0].range);
        for d in &decls[1..] {
            if self.sorts.leq(d.range, min) {
                min = d.range;
            }
            if self.sorts.leq(max, d.range) {
                max = d.range;
            }
        }
        let special = match value {
            NaValue::Str(s) => s.chars().count() == 1,
            NaValue::Float(bits) => f64::from_bits(*bits).is_finite(),
            NaValue::Qid(_) => true,
        };
        if special {
            min
        } else {
            max
        }
    }

    /// [`compute_sort`](Self::compute_sort) plus the **preregularity** bit: `true` iff the least sort
    /// is unique (the running down-set intersection equals the chosen range's down-set — Maude's
    /// `unique` flag). Maude *warns* when this is false; we compute it but defer the user-facing
    /// warning (no diagnostics sink yet) — the tie-break itself is exercised by conformance.
    pub(crate) fn compute_sort_uniq(&self, symbol: SymbolId, arg_sorts: &[SortId]) -> (SortId, bool) {
        let decls = self.symbols.get(symbol).decls();
        assert_eq!(
            arg_sorts.len(),
            decls[0].domain.len(),
            "arity mismatch building `{}`",
            self.symbols.get(symbol).name()
        );
        // Fast path: a single declaration (no overloading — every free/theory op in practice). Its
        // range is the unique least sort when applicable, else the kind's error sort. Avoids the
        // per-node down-set clone the general path does, keeping the reduce hot path allocation-free.
        if let [only] = decls {
            let applicable =
                arg_sorts.iter().zip(&only.domain).all(|(&a, &dom)| self.sorts.leq(a, dom));
            return if applicable {
                (only.range, true)
            } else {
                (self.sorts.error_sort(self.sorts.kind_of(only.range)), true)
            };
        }
        debug_assert!(
            decls.iter().all(|d| self.sorts.kind_of(d.range) == self.sorts.kind_of(decls[0].range)),
            "cross-kind ad-hoc overloading of `{}` is not yet supported (a B2 follow-up): the args, \
             not the range, would select the declaration group",
            self.symbols.get(symbol).name()
        );
        // Walk declarations in order, intersecting applicable range down-sets. `running` is the
        // down-set of the GLB so far; `min_range` is the earliest range that is <= everything so far.
        let mut min_range: Option<SortId> = None;
        let mut running: Option<std::collections::BTreeSet<SortId>> = None;
        for d in decls {
            if !arg_sorts.iter().zip(&d.domain).all(|(&a, &dom)| self.sorts.leq(a, dom)) {
                continue; // declaration not applicable to these argument sorts
            }
            let down = self.sorts.down_set(d.range);
            match &mut running {
                None => {
                    running = Some(down.clone());
                    min_range = Some(d.range);
                }
                Some(r) => {
                    r.retain(|x| down.contains(x)); // intersect with this range's down-set
                    if *r == *down {
                        min_range = Some(d.range); // d.range <= everything so far ⇒ new minimum
                    }
                }
            }
        }
        match min_range {
            // unique iff the GLB's down-set (`running`) equals the chosen min's down-set ⇒ min is the GLB.
            Some(r) => (r, running.as_ref() == Some(self.sorts.down_set(r))),
            None => (self.sorts.error_sort(self.sorts.kind_of(decls[0].range)), true),
        }
    }

    /// Least sort of a theory (ACU/AU/CUI) node, folding the **binary** [`compute_sort`](Self::compute_sort)
    /// left-to-right over the canonical element sorts (Maude's `traverse(traverse(0, i1), i2)`). For the
    /// single binary declaration `[D, D] -> R` every B1 / conformance operator carries, this returns `R`
    /// iff all elements `<= D` (else the kind's error sort) — identical to the old per-theory
    /// `compute_*_sort` — and extends to subsort-overloaded AC later with no reshape. `elem_sorts` is
    /// non-empty (a canonical theory node holds ≥ 2 elements).
    pub(crate) fn compute_sort_fold(&self, symbol: SymbolId, elem_sorts: &[SortId]) -> SortId {
        let mut acc = elem_sorts[0];
        for &e in &elem_sorts[1..] {
            acc = self.compute_sort(symbol, &[acc, e]);
        }
        acc
    }

    /// Least sort of an **S** node `s^count(arg)` (Maude's `S_Symbol::computeBaseSort` /
    /// `SortPath::computeSortIndex`). The successor's unary sort function, iterated over the argument
    /// sort, is eventually periodic (it maps a finite kind into itself), so the sort follows a **lead**
    /// prefix then a **cycle**: `count` in the lead indexes the prefix directly, beyond it indexes into
    /// the cycle. For NAT (`s_ : Nat -> NzNat`) the path is `Zero ↦ NzNat ↦ NzNat …`, so `s^n(0)` is
    /// `NzNat` for every `n >= 1`. Correctness-first: the path is recomputed per call (Maude precomputes
    /// a `sortPathTable` per argument sort — a perf follow-up).
    pub(crate) fn compute_s_sort(&self, symbol: SymbolId, arg_sort: SortId, count: &Nat) -> SortId {
        let (seq, lead) = self.s_sort_path(symbol, arg_sort);
        let path_len = seq.len();
        // An S node always has count >= 1. The first `path_len` successors index the path directly.
        if let Some(c) = count.to_usize()
            && c <= path_len
        {
            return seq[c - 1];
        }
        // Past the lead: index into the cycle (Maude's `computeSortIndex` tail arithmetic).
        let cycle = path_len - lead;
        let steps =
            count.checked_sub(&Nat::from_u64((lead + 1) as u64)).expect("count > path_len >= lead+1");
        seq[lead + steps.rem_usize(cycle)]
    }

    /// The successor sort path from `arg_sort`: `seq[k]` = least sort of `s^(k+1)(arg)`, iterating the
    /// unary [`compute_sort`](Self::compute_sort) until a sort repeats; returns `(seq, lead)` where
    /// `lead` is the index at which the cycle begins. Pigeonhole-terminating (finite kind).
    fn s_sort_path(&self, symbol: SymbolId, arg_sort: SortId) -> (Vec<SortId>, usize) {
        let mut seq: Vec<SortId> = Vec::new();
        let mut cur = arg_sort;
        loop {
            cur = self.compute_sort(symbol, &[cur]);
            if let Some(p) = seq.iter().position(|&s| s == cur) {
                return (seq, p);
            }
            seq.push(cur);
        }
    }

    /// Register an unconditional equation, compiling its lhs to a theory `LhsAutomaton` once, and
    /// advance the equation epoch (see [`Engine::add_equation`]).
    pub(crate) fn add_equation(&mut self, eq: Equation) -> u32 {
        self.push_equation(eq.lhs, eq.rhs, eq.nr_vars, Vec::new(), false)
    }

    /// Register a conditional equation `ceq lhs = rhs if condition` (B2.3): the condition is a list of
    /// [`ConditionFragment`]s (equality / sort-test), all of which must hold; a failure backtracks into
    /// the next matcher solution. `eq` stays the unconditional entry point (empty condition).
    pub(crate) fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_equation(lhs, rhs, nr_vars, condition, false)
    }

    /// Register an `[owise]` equation (optionally conditional): tried only if no non-owise equation of
    /// the symbol applies (Maude's `applyReplaceNoOwise` two-phase matching, B2.3b).
    pub(crate) fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_equation(lhs, rhs, nr_vars, condition, true)
    }

    /// Compile and register an equation, returning its dense per-module **id** (the index the frontend
    /// keys its trace metadata by).
    fn push_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
        owise: bool,
    ) -> u32 {
        let top = lhs.top_symbol().expect("equation lhs must be an application");
        let id = self.next_eq_id;
        self.next_eq_id += 1;
        let rhs_shares = term_has_repeated_subterm(&rhs);
        let compiled = CompiledEquation {
            id,
            lhs: LhsAutomaton::compile(lhs, self),
            rhs,
            nr_vars,
            condition: self.compile_condition(condition, CondOwner::EqOrMb),
            owise,
            rhs_shares,
        };
        self.equations.entry(top).or_default().push(compiled);
        // A term canonical under the old equation set may now be reducible: invalidate every
        // node's cached "reduced" stamp by advancing the epoch (review R2 H2).
        self.eq_epoch += 1;
        id
    }

    /// Compile a condition (public [`ConditionFragment`]s) for evaluation: equality / sort-test fragments
    /// are stored as-is; a matching (`:=`) or rewrite (`=>`) fragment's pattern is compiled to an
    /// [`LhsAutomaton`] through the same A3 seam (and F-A guard) as an equation lhs. `owner` gates the
    /// **rewrite** (`=>`) fragment, which is legal only in a rule condition — the frontend rejects it in
    /// an `ceq`/`cmb` (this is the defensive kernel backstop, A-v).
    fn compile_condition(&self, condition: Vec<ConditionFragment>, owner: CondOwner) -> Vec<CompiledFragment> {
        condition
            .into_iter()
            .map(|frag| match frag {
                ConditionFragment::Equality { lhs, rhs } => CompiledFragment::Equality { lhs, rhs },
                ConditionFragment::SortTest { term, sort } => CompiledFragment::SortTest { term, sort },
                ConditionFragment::Matching { pattern, subject, fresh_vars } => {
                    CompiledFragment::Matching {
                        pattern: LhsAutomaton::compile(pattern, self),
                        subject,
                        fresh_vars,
                    }
                }
                ConditionFragment::Rewrite { lhs, pattern, fresh_vars } => {
                    assert!(
                        owner == CondOwner::Rule,
                        "a rewrite (`=>`) condition fragment is legal only in a rule (`crl`)"
                    );
                    CompiledFragment::Rewrite {
                        lhs,
                        pattern: LhsAutomaton::compile(pattern, self),
                        fresh_vars,
                    }
                }
            })
            .collect()
    }

    /// Register an unconditional rule `rl lhs => rhs` (Pillar A). Compiles the lhs to a theory
    /// [`LhsAutomaton`] through the same A3 seam as an equation, and stores it in the [`rules`](Self::rules)
    /// table — never consulted by [`reduce`](Engine::reduce), so equational reduction can never apply it.
    pub(crate) fn add_rule(&mut self, lhs: Term, rhs: Term, nr_vars: u32) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, Vec::new())
    }

    /// Register a conditional rule `crl lhs => rhs if condition` (Pillar A-iii/A-v): the condition is the
    /// same [`ConditionFragment`] list as `ceq`, and a rule condition may *additionally* contain a
    /// **rewrite** fragment `t => p` (A-v). All fragments must hold; a failure backtracks into the next
    /// matcher solution.
    pub(crate) fn add_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_rule(lhs, rhs, nr_vars, condition)
    }

    /// Compile and register a rule, returning its dense per-module **id** (the index the frontend keys
    /// its `rl_traces` metadata by). Mirrors [`push_equation`](Self::push_equation) minus the `owise`
    /// phase and — crucially — **without** bumping `eq_epoch`: a rule cannot change any equational normal
    /// form, so invalidating the reduced-cache would be a pure regression.
    fn push_rule(&mut self, lhs: Term, rhs: Term, nr_vars: u32, condition: Vec<ConditionFragment>) -> u32 {
        let top = lhs.top_symbol().expect("rule lhs must be an application");
        let id = self.next_rule_id;
        self.next_rule_id += 1;
        let rhs_shares = term_has_repeated_subterm(&rhs);
        let compiled = CompiledRule {
            id,
            lhs: LhsAutomaton::compile(lhs, self),
            rhs,
            nr_vars,
            condition: self.compile_condition(condition, CondOwner::Rule),
            rhs_shares,
        };
        self.rules.entry(top).or_default().push(compiled);
        id
    }

    /// Register an (unconditional) membership axiom `mb lhs : sort`, compiling its lhs to a theory
    /// [`LhsAutomaton`] and indexing it by the lhs top symbol. A node's least sort is constrained at
    /// construction, so — like overload declarations — **memberships must be declared before any node
    /// of their lhs's symbol is built** (a node built earlier keeps its un-constrained sort). Does not
    /// bump `eq_epoch`: memberships refine sorts, not the `reduced` cache.
    pub(crate) fn add_membership(&mut self, mb: Membership) -> u32 {
        self.push_membership(mb.lhs, mb.sort, mb.nr_vars, Vec::new())
    }

    /// Register a conditional membership `cmb lhs : sort if condition` (B2.3c): the sort is lowered
    /// only when the condition (the same [`ConditionFragment`]s as `ceq`) holds under the membership
    /// match's substitution. `mb` stays the unconditional entry point (empty condition).
    pub(crate) fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.push_membership(lhs, sort, nr_vars, condition)
    }

    /// Compile and register a membership axiom, returning its dense per-module **id**. (The membership
    /// table is re-sorted smallest-target-first for application, but `id` stays declaration order — the
    /// frontend keys `mb_traces` by it.)
    fn push_membership(&mut self, lhs: Term, sort: SortId, nr_vars: u32, condition: Vec<ConditionFragment>) -> u32 {
        let top = lhs.top_symbol().expect("membership lhs must be an application");
        let id = self.next_mb_id;
        self.next_mb_id += 1;
        let compiled = SortConstraint {
            id,
            lhs: LhsAutomaton::compile(lhs, self),
            sort,
            nr_vars,
            condition: self.compile_condition(condition, CondOwner::EqOrMb),
        };
        let sorts = &self.sorts;
        let v = self.memberships.entry(top).or_default();
        v.push(compiled);
        // Order smallest-target-sort first (subsorts before supersorts), so the constrain pass lowers
        // a node straight to its smallest applicable sort in ONE application — matching the membership
        // count Maude reports (Maude also tries smallest-sort-first).
        v.sort_by(|x, y| {
            if x.sort == y.sort {
                Ordering::Equal
            } else if sorts.leq(x.sort, y.sort) {
                Ordering::Less
            } else if sorts.leq(y.sort, x.sort) {
                Ordering::Greater
            } else {
                x.sort.cmp(&y.sort) // incomparable: deterministic tie-break (non-confluent is a follow-up)
            }
        });
        id
    }

    /// The current equation-set epoch (stamped into nodes proved canonical; see [`DagNode`]).
    pub(crate) fn eq_epoch(&self) -> u32 {
        self.eq_epoch
    }
}

// ======================================================================================
// Runtime: the DAG arena, GC, and the reduction subsystem (mutates; borrows the Signature)
// ======================================================================================

impl Runtime {
    // ---- DAG construction ----

    /// Allocate a node with its **base** (structural) sort, accounting it against the safe-point-GC
    /// interval. The universal allocator for every `make_*` builder: a freshly built node carries only
    /// its base sort — membership axioms (`mb`/`cmb`) are **not** applied here. Maude likewise gives a
    /// fresh `DagNode` no sort at construction (`SORT_UNKNOWN`) and refines it lazily at the reduce
    /// normal-form point (`DagNode::reduce` → `fastComputeTrueSort`); we keep the eager *base* sort (so
    /// `sort_of` stays a total read) but defer the membership refinement identically — see the C1
    /// normal-form step in [`reduce`](Self::reduce). (The alloc counter only matters when `gc_interval`
    /// is set, so the default path is a no-op increment. Reset by `safe_point_gc`, so it can't overflow.)
    fn alloc_node(&mut self, sort: SortId, term: NodeTerm) -> DagId {
        // C7 Half 1: inside a dedup window, collapse a structurally-identical node to the existing one.
        // A hit allocates nothing (so it must NOT bump the GC alloc counter — hence the `alloc_raw`
        // split). The `is_some()` guard is the only cost on the default reduce path.
        if self.dedup.is_some() {
            if let Some(&existing) = self.dedup.as_ref().unwrap().get(&term) {
                return existing;
            }
            let key = term.clone();
            let id = self.alloc_raw(sort, term);
            self.dedup.as_mut().unwrap().insert(key, id);
            return id;
        }
        self.alloc_raw(sort, term)
    }

    /// The raw allocation funnel: account the node against the safe-point-GC interval and allocate it
    /// fresh. Split out of [`alloc_node`](Self::alloc_node) so a dedup *hit* (which allocates nothing)
    /// bypasses the counter bump entirely.
    fn alloc_raw(&mut self, sort: SortId, term: NodeTerm) -> DagId {
        if self.gc_interval.is_some() {
            self.allocs_since_gc += 1;
        }
        self.dags.alloc(DagNode { sort, reduced_epoch: 0, nf: None, term })
    }

    /// Open a construction-time structural-dedup window (C7 Half 1): until [`end_dedup`](Self::end_dedup),
    /// every node built via [`alloc_node`](Self::alloc_node) is deduplicated, so a repeated subterm
    /// becomes one shared node. Must wrap a pure-construction span with **no GC safe point** inside (the
    /// memo holds raw ids), and must be balanced by `end_dedup`. Re-opening inside an open window is
    /// supported by save/restore at the call site (the rhs path); the bare pair simply resets to `None`.
    fn begin_dedup(&mut self) {
        self.dedup = Some(HashMap::new());
    }

    /// Close the dedup window opened by [`begin_dedup`](Self::begin_dedup), dropping the memo.
    fn end_dedup(&mut self) {
        self.dedup = None;
    }

    /// Lower `id`'s cached least sort by the membership axioms of its top symbol (Maude's
    /// `constrainToSmallerSort`): repeatedly find the first membership — they are ordered
    /// **smallest-target-sort first** by [`add_membership`](Signature::add_membership) — whose target
    /// is strictly below the node's current sort and whose lhs matches, lower the node's sort to it,
    /// and retry from the top, to a fixpoint. **Each lowering counts as one rewrite** (Maude counts
    /// membership applications in its `rewrites` total); the smallest-first order means a node drops
    /// straight to its smallest applicable sort in one application, matching Maude's count. Non-confluent
    /// membership sets (incomparable applicable targets) and matching modulo AC/`iter` are follow-ups.
    ///
    /// **Lazy timing (C1):** this is now called only at a node's reduce **normal-form point** (after its
    /// equations are exhausted), never at construction — mirroring Maude's `fastComputeTrueSort`. So a
    /// term an equation reduces away is never constrained (no over-count; a `cmb` whose condition loops
    /// never fires on a doomed redex). `whole` is the reconstructed root term for the `set trace whole`
    /// `Whole:` line (the caller threads `id` up its reduce frame stack); `None` when not whole-tracing.
    fn constrain_to_smaller_sort(&mut self, sig: &Signature, id: DagId, whole: Option<DagId>, frames: &[ReduceFrame]) {
        let symbol = self.node(id).symbol();
        let Some(constraints) = sig.memberships.get(&symbol) else { return };
        loop {
            let current = self.node(id).sort;
            let mut lowered = false;
            for sc in constraints {
                // Only a membership whose target is *strictly below* the current sort can refine it.
                if sc.sort == current || !sig.sorts().leq(sc.sort, current) {
                    continue;
                }
                if let Some(bindings) = self.membership_applies(sig, sc, id, frames) {
                    // Record BEFORE mutating the sort: the event captures the *old* (current) sort.
                    if self.tracing() {
                        let depth = self.condition_depth;
                        self.record(TraceEvent::Membership {
                            mb_id: sc.id,
                            depth,
                            subject: id,
                            old_sort: current,
                            new_sort: sc.sort,
                            bindings,
                            whole,
                        });
                    }
                    self.dags.get_mut(id).sort = sc.sort;
                    self.rewrite_count += 1; // a membership application counts as a rewrite (Maude)
                    lowered = true;
                    break; // restart the scan with the new, smaller sort
                }
            }
            if !lowered {
                break;
            }
        }
    }

    /// Whether the membership applies to node `id`: its compiled lhs matches *and* (for a `cmb`) its
    /// condition holds under that match. Reads through the A3 matcher seam, so a free lhs uses the
    /// recursive matcher and a theory lhs its own automaton. A condition that fails for one match
    /// solution backtracks into the next (B2.3c); the condition's own reductions count toward the
    /// rewrite total whether or not it ends up holding. (AC/`iter` membership matching is a follow-up.)
    /// On success returns the membership match's substitution snapshot (for the trace), or an empty
    /// `Vec` when not tracing (no allocation); `None` on no-match. A conditional membership (`cmb`) emits
    /// a *trial* per matcher solution, backtracking on condition failure.
    fn membership_applies(
        &mut self,
        sig: &Signature,
        sc: &SortConstraint,
        id: DagId,
        frames: &[ReduceFrame],
    ) -> Option<Vec<Option<DagId>>> {
        let mut subst = Subst::new();
        subst.reset(sc.nr_vars);
        let mut sp = sc.lhs.match_(self, sig, id, &mut subst, false)?;
        while sp.next(self, sig, &mut subst) {
            if sc.condition.is_empty() {
                return Some(if self.tracing() { Self::snapshot_subst(&subst) } else { Vec::new() });
            }
            let depth = self.condition_depth;
            if self.tracing() {
                let bindings = Self::snapshot_subst(&subst);
                self.record(TraceEvent::TrialStart {
                    kind: StmtKind::Membership,
                    stmt_id: sc.id,
                    depth,
                    bindings,
                });
            }
            let holds = self.condition_holds(
                sig,
                &sc.condition,
                &mut subst,
                StmtKind::Membership,
                sc.id,
                frames,
                id,
            );
            if self.tracing() {
                self.record(TraceEvent::TrialEnd {
                    kind: StmtKind::Membership,
                    depth,
                    success: holds,
                });
            }
            if holds {
                return Some(if self.tracing() { Self::snapshot_subst(&subst) } else { Vec::new() });
            }
        }
        None
    }

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub(crate) fn make_free(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        args: Vec<DagId>,
    ) -> DagId {
        // Keep the old `compute_free_sort` theory guard verbatim — its message must still name
        // `make_acu` (see `make_free_on_ac_operator_panics`); the arity check now lives in `compute_sort`.
        assert_eq!(
            sig.symbol(symbol).theory(),
            Theory::Free,
            "`{}` is an ACU operator — build it with make_acu/make_ac, not make_free",
            sig.symbol(symbol).name()
        );
        let sort = self.free_sort(sig, symbol, &args);
        self.alloc_node(sort, NodeTerm::Free { symbol, args })
    }

    /// Least sort of a free node `symbol(args…)`. The common case — a single declaration, no
    /// overloading — is computed **inline** with no allocation (the equivalent of the old
    /// `compute_free_sort`), keeping the reduce hot path fast; only an overloaded free operator falls
    /// back to the general [`Signature::compute_sort`], which needs the argument sorts as a slice.
    fn free_sort(&self, sig: &Signature, symbol: SymbolId, args: &[DagId]) -> SortId {
        let decls = sig.symbol(symbol).decls();
        if let [only] = decls {
            assert_eq!(
                args.len(),
                only.domain.len(),
                "arity mismatch building `{}`",
                sig.symbol(symbol).name()
            );
            let well_sorted = only
                .domain
                .iter()
                .zip(args)
                .all(|(&dom, &arg)| sig.sorts().leq(self.dags.get(arg).sort, dom));
            return if well_sorted {
                only.range
            } else {
                sig.sorts().error_sort(sig.sorts().kind_of(only.range))
            };
        }
        let arg_sorts: Vec<SortId> = args.iter().map(|&a| self.dags.get(a).sort).collect();
        sig.compute_sort(symbol, &arg_sorts)
    }

    /// Recompute `id`'s **base** (structural) sort from its current children's sorts — Maude's
    /// `computeBaseSort`, the pure membership-free part of `fastComputeTrueSort`. Mirrors the per-theory
    /// sort each `make_*` builder computes, but reads the *existing* (already-canonical) node instead of
    /// rebuilding it. The C1 reduce normal-form step calls this before constraining: a child refined in
    /// place at its own normal-form point does **not** propagate to a parent that was not rebuilt (the
    /// reduce loop keeps `original` when `args == orig`), so the parent must recompute its base sort from
    /// the now-refined children here. A pure function of the children's sorts ⇒ idempotent. An `Na`
    /// constant has no children, so its base sort never changes (kept as-is).
    fn compute_base_sort(&self, sig: &Signature, id: DagId) -> SortId {
        match &self.node(id).term {
            NodeTerm::Free { symbol, args } => self.free_sort(sig, *symbol, args),
            NodeTerm::Acu { symbol, args } => {
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
                    .collect();
                sig.compute_sort_fold(*symbol, &elem_sorts)
            }
            NodeTerm::Au { symbol, args } => {
                let arg_sorts: Vec<SortId> = args.iter().map(|&e| self.dags.get(e).sort).collect();
                sig.compute_sort_fold(*symbol, &arg_sorts)
            }
            NodeTerm::Cui { symbol, args } => {
                sig.compute_sort(*symbol, &[self.dags.get(args[0]).sort, self.dags.get(args[1]).sort])
            }
            NodeTerm::S { symbol, count, arg } => {
                sig.compute_s_sort(*symbol, self.dags.get(*arg).sort, count)
            }
            NodeTerm::Na { .. } => self.node(id).sort,
        }
    }

    /// Refine `id`'s sort — and recursively its subterms' — to their **true sorts** without applying any
    /// equations: Maude's `DagNode::computeTrueSort`. The C1 seam-3 counterpart to the reduce normal-form
    /// step, for **strat-skipped** args: a custom evaluation strategy (`strat`) never reduces them, so
    /// they never reach a reduce normal-form point — yet Maude's `complexStrategy` calls `computeTrueSort`
    /// on *all* args at the strat `0` step (`FreeTheory/freeSymbol.cc:503`), refining even the skipped
    /// ones. We mirror that: recurse into the children, recompute this node's base sort from the
    /// now-refined children, then constrain by its memberships (each application counts, as Maude counts
    /// membership applications).
    ///
    /// `seen` dedupes shared subterms reached within one strat node (e.g. an instantiated `f(X, X)` whose
    /// two slots are the same node), so such a node is refined — and its membership counted — exactly
    /// once, matching Maude (whose `slowComputeTrueSort` no-ops once a node's sort is known). An
    /// already-reduced node carries its true sort, so it is skipped too. (A node shared as a *skipped arg
    /// across two separate strat frames* in one reduction would be refined once per frame — a narrow edge
    /// needing `strat` + `mb` + a repeated strat-skipped compound. C7's construction dedup can now produce
    /// such sharing, but no observed case hits it; see `gaps.md`.)
    fn compute_true_sort(&mut self, sig: &Signature, id: DagId, seen: &mut HashSet<DagId>, frames: &[ReduceFrame]) {
        if self.node(id).reduced_epoch == sig.eq_epoch() || !seen.insert(id) {
            return; // already at its true sort, or already refined in this pass
        }
        let children: Vec<DagId> = self.node(id).children().collect();
        for c in children {
            self.compute_true_sort(sig, c, seen, frames);
        }
        let base = self.compute_base_sort(sig, id);
        self.dags.get_mut(id).sort = base;
        // No reduce frame here (this is off the main stack), so no `Whole:` reconstruction — `None`. `frames`
        // is the enclosing reduce's stack: an F-2 root set for a `cmb` condition that re-enters `reduce`.
        self.constrain_to_smaller_sort(sig, id, None, frames);
    }

    /// Convenience for a constant (an arity-0 symbol).
    pub(crate) fn make_const(&mut self, sig: &Signature, symbol: SymbolId) -> DagId {
        self.make_free(sig, symbol, Vec::new())
    }

    /// Build a canonical **ACU** node for `symbol` from `raw_args` (`(element, multiplicity)` pairs).
    /// Canonicalizes to the AC(+U) normal form (Maude's `normalizeAtTop` → `insertAlien` →
    /// `sortAndUniquize`): (1) flatten arguments that are themselves `symbol`-rooted ACU nodes (scaling
    /// their multiplicities), (2) drop identity elements when the operator has `id:`, (3) merge equal
    /// elements (summing multiplicities) and sort by [`dag_compare`](Self::dag_compare), (4) collapse —
    /// an empty multiset is the identity element, a single element of multiplicity 1 is that element
    /// itself, otherwise an [`NodeTerm::Acu`] node. So the result is in normal form and equal ACU terms
    /// are structurally identical through the [`children`](crate::dag::DagNode::children) visitor.
    pub(crate) fn make_acu(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        raw_args: Vec<(DagId, u32)>,
    ) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Acu, "make_acu on a non-ACU symbol");
        let identity = sig.symbol(symbol).identity();

        // (1) flatten nested same-symbol nodes + (2) drop identity elements.
        let mut flat: Vec<(DagId, u32)> = Vec::with_capacity(raw_args.len());
        for (arg, mult) in raw_args {
            if mult == 0 {
                continue;
            }
            if identity.is_some_and(|id_sym| self.is_constant(arg, id_sym)) {
                continue; // an identity argument vanishes
            }
            match &self.dags.get(arg).term {
                NodeTerm::Acu { symbol: inner, args } if *inner == symbol => {
                    for &(e, m) in args {
                        flat.push((e, m * mult));
                    }
                }
                _ => flat.push((arg, mult)),
            }
        }

        // (3) sort by the total order, then merge structurally-equal neighbours (summing mults).
        flat.sort_by(|&(x, _), &(y, _)| self.dag_compare(x, y));
        let mut args: Vec<(DagId, u32)> = Vec::with_capacity(flat.len());
        for (e, m) in flat {
            match args.last_mut() {
                Some(last) if self.dag_compare(last.0, e) == Ordering::Equal => last.1 += m,
                _ => args.push((e, m)),
            }
        }

        // (4) collapse to the canonical representative.
        let total: u64 = args.iter().map(|&(_, m)| u64::from(m)).sum();
        match total {
            0 => {
                let id_sym = identity.expect("an empty ACU multiset requires an identity element");
                self.make_const(sig, id_sym)
            }
            1 => args[0].0, // exactly one element, multiplicity 1 — never wrap a lone argument
            _ => {
                // Fold the binary least-sort over the multiset elements (with multiplicity repeats),
                // mirroring Maude's `traverse(traverse(0, i1), i2)` over the flattened arguments.
                let elem_sorts: Vec<SortId> = args
                    .iter()
                    .flat_map(|&(e, m)| std::iter::repeat_n(self.dags.get(e).sort, m as usize))
                    .collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node(sort, NodeTerm::Acu { symbol, args })
            }
        }
    }

    /// Build a canonical **AU** node for `symbol` from `raw_args` (an ordered argument list). Mirrors
    /// [`make_acu`](Self::make_acu) for the associative-only theory: flatten arguments that are
    /// themselves `symbol`-rooted AU nodes (preserving order), drop identity elements, then collapse —
    /// empty → the identity, a single argument → that argument, else an [`NodeTerm::Au`] node. Order is
    /// significant, so there is **no** sorting or multiplicity merging.
    pub(crate) fn make_au(&mut self, sig: &Signature, symbol: SymbolId, raw_args: Vec<DagId>) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Au, "make_au on a non-AU symbol");
        let identity = sig.symbol(symbol).identity();
        let mut args: Vec<DagId> = Vec::with_capacity(raw_args.len());
        for arg in raw_args {
            if identity.is_some_and(|id_sym| self.is_constant(arg, id_sym)) {
                continue; // an identity argument vanishes
            }
            match &self.dags.get(arg).term {
                NodeTerm::Au { symbol: inner, args: inner_args } if *inner == symbol => {
                    args.extend_from_slice(inner_args);
                }
                _ => args.push(arg),
            }
        }
        match args.len() {
            0 => {
                let id_sym = identity.expect("an empty AU sequence requires an identity element");
                self.make_const(sig, id_sym)
            }
            1 => args[0],
            _ => {
                let elem_sorts: Vec<SortId> = args.iter().map(|&e| self.dags.get(e).sort).collect();
                let sort = sig.compute_sort_fold(symbol, &elem_sorts);
                self.alloc_node(sort, NodeTerm::Au { symbol, args })
            }
        }
    }

    /// Build a canonical **CUI** node for `symbol` from its two arguments. Applies the collapse axioms
    /// at construction (Maude keeps CUI terms in normal form): an identity argument (`id:`) drops the
    /// node to the other argument; idempotence (`idem`) drops `f(a, a)` to `a`; otherwise the two
    /// arguments are placed in canonical (sorted) order for commutativity. So `f(b, a)` and `f(a, b)`
    /// are the same node, and `f(a, a)`/`f(a, e)` collapse away for free (0 rewrites).
    pub(crate) fn make_cui(
        &mut self,
        sig: &Signature,
        symbol: SymbolId,
        mut x: DagId,
        mut y: DagId,
    ) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::Cui, "make_cui on a non-CUI symbol");
        let identity = sig.symbol(symbol).identity;
        let idem = sig.symbol(symbol).axioms.idem;
        if let Some(id_sym) = identity {
            if self.is_constant(x, id_sym) {
                return y;
            }
            if self.is_constant(y, id_sym) {
                return x;
            }
        }
        if idem && self.dag_compare(x, y) == Ordering::Equal {
            return x;
        }
        if self.dag_compare(x, y) == Ordering::Greater {
            std::mem::swap(&mut x, &mut y); // canonical order for commutativity
        }
        let sort = sig.compute_sort(symbol, &[self.dags.get(x).sort, self.dags.get(y).sort]);
        self.alloc_node(sort, NodeTerm::Cui { symbol, args: vec![x, y] })
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)` (Maude's `S_DagNode::normalizeAtTop`):
    /// `count == 0` collapses to `arg` (`s^0(x) = x`); a nested same-symbol successor flattens
    /// (`s^j(s^k(x)) = s^(j+k)(x)` — one level suffices, the inner node is already normalized); otherwise
    /// an [`NodeTerm::S`] with the periodic least sort ([`compute_s_sort`](Signature::compute_s_sort)).
    pub(crate) fn make_s(&mut self, sig: &Signature, symbol: SymbolId, count: Nat, arg: DagId) -> DagId {
        debug_assert_eq!(sig.symbol(symbol).theory(), Theory::S, "make_s on a non-S symbol");
        if count.is_zero() {
            return arg;
        }
        let (count, arg) = match &self.dags.get(arg).term {
            NodeTerm::S { symbol: inner, count: k, arg: inner_arg } if *inner == symbol => {
                (count.add(k), *inner_arg)
            }
            _ => (count, arg),
        };
        let arg_sort = self.dags.get(arg).sort;
        let sort = sig.compute_s_sort(symbol, arg_sort, &count);
        self.alloc_node(sort, NodeTerm::S { symbol, count, arg })
    }

    /// Build an atomic **NA** constant node carrying `value` (a string/qid/float). The sort is
    /// `symbol`'s range (`symbol` is an arity-0 NA-constant symbol — Maude's `StringSymbol` etc.).
    pub(crate) fn make_na(&mut self, sig: &Signature, symbol: SymbolId, value: NaValue) -> DagId {
        let sort = sig.compute_na_sort(symbol, &value);
        self.alloc_node(sort, NodeTerm::Na { symbol, value })
    }

    /// Rebuild a node for `symbol` from `children` (the flattened child sequence), dispatching on the
    /// operator's theory: a free node directly, or a canonical ACU/AU/CUI/S node. Used by `reduce` when a
    /// child changed and by `instantiate`, so neither hard-codes the free constructor (which rejects
    /// theory symbols).
    pub(crate) fn rebuild(&mut self, sig: &Signature, symbol: SymbolId, children: Vec<DagId>) -> DagId {
        match sig.symbol(symbol).theory() {
            Theory::Free => self.make_free(sig, symbol, children),
            Theory::Acu => self.make_acu(sig, symbol, children.into_iter().map(|d| (d, 1)).collect()),
            Theory::Au => self.make_au(sig, symbol, children),
            Theory::Cui => {
                debug_assert_eq!(children.len(), 2, "a CUI node is binary");
                self.make_cui(sig, symbol, children[0], children[1])
            }
            // An iter `Op` layer (from `instantiate`) is one successor; `make_s` flattening folds nested
            // layers into a single `s^k`. `reduce` re-seats existing S nodes with their preserved count
            // directly (not through here), so this `s^1` semantics is only ever what `instantiate` wants.
            Theory::S => {
                debug_assert_eq!(children.len(), 1, "an S successor is unary");
                self.make_s(sig, symbol, Nat::one(), children[0])
            }
        }
    }

    /// Whether `arg` is the constant `id_sym()` (an arity-0 free node). Used to recognise identity
    /// arguments during ACU canonicalization.
    fn is_constant(&self, arg: DagId, id_sym: SymbolId) -> bool {
        matches!(
            &self.dags.get(arg).term,
            NodeTerm::Free { symbol, args } if *symbol == id_sym && args.is_empty()
        )
    }

    /// A **total order** on DAG nodes, consistent with structural (modulo-AC) equality — i.e.
    /// `dag_compare(a, b) == Equal` iff [`deep_equal`](Self::deep_equal)`(a, b)`. Mirrors C++
    /// `DagNode::compare`: order by top symbol first, then lexicographically by arguments (ACU nodes
    /// compare their canonical `(element, multiplicity)` sequences). This is the key the ACU
    /// canonicalizer sorts and uniquizes by. Recurses on *element* depth (like `match_pattern`,
    /// author-/data-shallow for the canonical subterms it compares); an iterative form is a follow-up
    /// if deep ACU elements ever appear.
    pub(crate) fn dag_compare(&self, a: DagId, b: DagId) -> Ordering {
        if a == b {
            return Ordering::Equal; // same node id — identical, prune
        }
        let (na, nb) = (self.dags.get(a), self.dags.get(b));
        match na.symbol().cmp(&nb.symbol()) {
            Ordering::Equal => {}
            ord => return ord,
        }
        // Equal top symbols ⇒ the same theory ⇒ the same `NodeTerm` arm.
        match (&na.term, &nb.term) {
            (NodeTerm::Free { args: xa, .. }, NodeTerm::Free { args: ya, .. }) => {
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(x, y) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                Ordering::Equal // same symbol ⇒ same arity ⇒ all pairs compared
            }
            (NodeTerm::Acu { args: xa, .. }, NodeTerm::Acu { args: ya, .. }) => {
                for (&(xe, xm), &(ye, ym)) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(xe, ye) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                    match xm.cmp(&ym) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                xa.len().cmp(&ya.len()) // a proper prefix orders before the longer sequence
            }
            // AU (ordered sequence) and CUI (canonically-ordered pair) compare the same way: an equal
            // top symbol means the same arm, so the cross cases can't arise.
            (NodeTerm::Au { args: xa, .. }, NodeTerm::Au { args: ya, .. })
            | (NodeTerm::Cui { args: xa, .. }, NodeTerm::Cui { args: ya, .. }) => {
                for (&x, &y) in xa.iter().zip(ya.iter()) {
                    match self.dag_compare(x, y) {
                        Ordering::Equal => {}
                        ord => return ord,
                    }
                }
                xa.len().cmp(&ya.len()) // lexicographic, then by length
            }
            // S successor: the scalar `count` is part of identity (not a child), so compare it first,
            // then the argument (Maude's `S_DagNode::compareArguments`). This keeps the order consistent
            // with the `deep_equal` S-arm, so `s^2(0)` and `s^3(0)` order correctly inside an ACU subject.
            (NodeTerm::S { count: xc, arg: xa, .. }, NodeTerm::S { count: yc, arg: ya, .. }) => {
                match xc.cmp(yc) {
                    Ordering::Equal => self.dag_compare(*xa, *ya),
                    ord => ord,
                }
            }
            // An NA constant orders by its scalar value (consistent with the `deep_equal` Na arm).
            (NodeTerm::Na { value: xv, .. }, NodeTerm::Na { value: yv, .. }) => xv.cmp(yv),
            _ => unreachable!("equal top symbols must share a NodeTerm arm"),
        }
    }

    pub(crate) fn node(&self, id: DagId) -> &DagNode {
        self.dags.get(id)
    }
    pub(crate) fn sort_of(&self, id: DagId) -> SortId {
        self.dags.get(id).sort
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub(crate) fn live_nodes(&self) -> usize {
        self.dags.len()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub(crate) fn node_capacity(&self) -> usize {
        self.dags.capacity()
    }

    // ---- garbage collection (D2) ----

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives (see [`Engine::root`]).
    pub(crate) fn root(&self, id: DagId) -> RootGuard {
        RootGuard::new(&self.roots, id)
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`] or from `extra_roots`
    /// (see [`Engine::gc`]); returns the number reclaimed.
    pub(crate) fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.dags.clear_marks();
        self.mark_registered_roots();
        for root in extra_roots {
            self.mark_reachable(root);
        }
        self.dags.sweep(|_| {})
    }

    /// Mark (transitively) every root currently pinned by a [`RootGuard`].
    fn mark_registered_roots(&mut self) {
        // Collect first so the registry borrow is released before the `&mut self` mark walk.
        let pinned: Vec<DagId> = self.roots.borrow().live_roots().collect();
        for r in pinned {
            self.mark_reachable(r);
        }
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Engine::reduce) (see
    /// [`Engine::set_gc_interval`] for the rooting contract).
    pub(crate) fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.gc_interval = interval;
    }

    /// Collect at a `reduce` safe point, rooting the in-flight working set: the registry, plus every
    /// frame's term (`original`, which transitively covers its unreduced `orig` children) and its
    /// current `args` (the strategy-reduced positions are fresh nodes not reachable from `original`),
    /// plus the `child_result` not yet delivered into a frame. This is the complete loop-head root set
    /// (see the [`ReduceFrame`] safe-point contract); collecting anywhere else would miss fresh nodes
    /// living only in native-stack locals.
    fn safe_point_gc(&mut self, frames: &[ReduceFrame], child_result: Option<DagId>) {
        self.dags.clear_marks();
        self.mark_registered_roots();
        for frame in frames {
            self.mark_reachable(frame.original);
            // `start` is the node this frame will memoize at completion (C7 forwarding). Once the frame
            // has rewritten, `start` is the *abandoned* original redex — no longer in the live structure,
            // referenced only here — so it must be rooted, or GC reclaims it and the completion's
            // `nf` write is a use-after-free. When `start == original` this is a redundant (deduped) mark.
            self.mark_reachable(frame.start);
            for &r in &frame.args {
                self.mark_reachable(r);
            }
        }
        if let Some(r) = child_result {
            self.mark_reachable(r);
        }
        // A trace holds intermediate node ids (redex/result/bindings/subject/whole, incl. of failed
        // condition trials) for later rendering — root them all so a traced reduction under in-reduction
        // GC keeps them alive. (Collected first to release the shared borrow before `mark_reachable`
        // takes `&mut self`; `None` on the common untraced path.)
        if let Some(trace) = &self.trace {
            let mut ids: Vec<DagId> = Vec::new();
            for ev in trace {
                ev.for_each_id(|d| ids.push(d));
            }
            for id in ids {
                self.mark_reachable(id);
            }
        }
        // F-2: the outer reduction(s)' working set, protected across any re-entrant condition reduce we
        // are nested inside (`condition_holds` pushed it). Without this a nested condition-GC would sweep
        // the outer frames' siblings / match bindings / redex. (Cloned to release the borrow before
        // `mark_reachable` takes `&mut self`; empty — a no-op — unless we are inside a condition.)
        if !self.protected.is_empty() {
            let protected = self.protected.clone();
            for id in protected {
                self.mark_reachable(id);
            }
        }
        self.dags.sweep(|_| {});
    }

    /// Iterative (stack-based) transitive marker. Marks each node **on push** (using the
    /// "newly-marked" result of [`Arena::mark`]) so a node shared by *k* parents is pushed once,
    /// keeping the work stack O(nodes) rather than O(edges); it also terminates on shared/cyclic
    /// structure.
    fn mark_reachable(&mut self, root: DagId) {
        let mut stack = Vec::new();
        // Children are collected (via the `children()` visitor) into this reused scratch buffer, then
        // marked: enumerating borrows the node (hence the arena) immutably, while marking needs the
        // arena mutably, so the two phases can't overlap. `extend` from the iterator hits a slice
        // fast-path for the free rep; a non-slice arm still works, just without the memcpy.
        let mut kids: Vec<DagId> = Vec::new();
        if self.dags.mark(root) {
            stack.push(root);
        }
        while let Some(id) = stack.pop() {
            kids.clear();
            kids.extend(self.dags.get(id).children());
            // A reduced node's forwarding normal form (C7 `nf`) is not a structural child — `g(a)`'s
            // child is `a`, not its result `b` — so the `children()` visitor misses it; mark it here so
            // a node that is still reachable keeps the result it forwards to alive (freed together).
            if let Some(nf) = self.dags.get(id).nf {
                kids.push(nf);
            }
            for &child in &kids {
                if self.dags.mark(child) {
                    stack.push(child);
                }
            }
        }
    }

    // ---- statistics ----

    /// Total equational rewrites applied so far.
    pub(crate) fn rewrites(&self) -> u64 {
        self.rewrite_count
    }
    pub(crate) fn reset_rewrites(&mut self) {
        self.rewrite_count = 0;
    }

    // ---- reduction ----

    /// The reduction core; see [`Engine::reduce`] for the contract and the iterative-vs-recursive
    /// rationale. Reads `sig.eq_epoch()`, builds nodes via `self.make_free(sig, ..)`, and rewrites
    /// the top via `self.try_rewrite_top(sig, ..)` — all while holding only a shared borrow of `sig`.
    #[must_use]
    pub(crate) fn reduce(&mut self, sig: &Signature, root: DagId) -> DagId {
        if self.node(root).reduced_epoch == sig.eq_epoch() {
            // Already normal: forward to its recorded nf (C7) — `root`'s own content may be a redex that
            // rewrote out of place, so the nf, not `root`, is its canonical form (`None` ⇒ self).
            return self.node(root).nf.unwrap_or(root);
        }

        let mut stack: Vec<ReduceFrame> = Vec::new();
        stack.push(self.new_reduce_frame(root));
        // Carries a just-completed child's normal form up to the parent frame waiting on it.
        let mut child_result: Option<DagId> = None;

        loop {
            // Invariant: `stack` is non-empty throughout the body. It starts with the root frame and
            // the only `pop` (below) is immediately followed by a `return` when it empties, so the
            // loop never re-enters with an empty stack — the `expect`s below are therefore unreachable.

            // Safe-point GC (A2): the loop head is the *only* point during a reduction where every
            // in-flight node is discoverable (the frame stack + `child_result`); collect here when
            // allocation pressure crosses the configured interval so a large reduction stays bounded.
            if let Some(interval) = self.gc_interval
                && self.allocs_since_gc >= interval
            {
                self.safe_point_gc(&stack, child_result);
                self.allocs_since_gc = 0;
            }

            // Deliver a completed child into its strategy position and advance the strategy cursor.
            if let Some(r) = child_result.take() {
                let f = stack.last_mut().expect("child result with empty reduce stack");
                let pos = sig
                    .strat_position(f.symbol, f.cursor, f.orig.len())
                    .expect("delivering a child means a strategy step was in progress");
                f.args[pos] = r;
                f.cursor += 1;
            }

            // Phase 1: reduce the next argument the strategy selects (the standard strategy walks them
            // left-to-right; a custom strategy reduces only its listed positions). Already-reduced
            // children (shared subterms, cached by epoch) are delivered without pushing a frame.
            {
                let f = stack.last().expect("empty reduce stack");
                if let Some(pos) = sig.strat_position(f.symbol, f.cursor, f.orig.len()) {
                    let child = f.args[pos];
                    if self.node(child).reduced_epoch == sig.eq_epoch() {
                        // Already-reduced (a shared subterm, cached by epoch): deliver its normal form
                        // without pushing a frame. Forward through `nf` (C7) so a shared redex that
                        // rewrote out of place delivers its result, not its stale content (`None` ⇒ self).
                        child_result = Some(self.node(child).nf.unwrap_or(child));
                    } else {
                        let frame = self.new_reduce_frame(child);
                        stack.push(frame);
                    }
                    continue;
                }
            }

            // C1 seam 3 — a custom evaluation strategy (`strat`) leaves some args unreduced, so they
            // never reach a reduce normal-form point; Maude's `complexStrategy` still computes their true
            // sort at the strat `0` step. Refine the (skipped) args' sorts here — no equations — so the
            // rebuild's base-sort recompute and the top-rewrite matching below see the same sorts Maude
            // does. Gated on a custom strat + the module having memberships: the standard strategy reduces
            // every arg (each refined at its own normal-form point), and a membership-free module never
            // changes a sort, so both keep the unchanged hot path. Already-reduced args no-op (guarded).
            if !sig.memberships.is_empty()
                && sig.symbol(stack.last().expect("empty reduce stack").symbol).strategy.is_some()
            {
                let args = stack.last().expect("empty reduce stack").args.clone();
                let mut seen = HashSet::new();
                for arg in args {
                    self.compute_true_sort(sig, arg, &mut seen, &stack);
                }
            }

            // Phase 1 complete (strategy exhausted): rebuild iff some argument changed, else keep the id.
            let (symbol, original, args, changed) = {
                let f = stack.last_mut().expect("empty reduce stack");
                let changed = f.args != f.orig;
                // `mem::take` moves the args out (no clone) — the frame is about to be reused or popped,
                // so its `args` is no longer needed.
                let args = if changed { std::mem::take(&mut f.args) } else { Vec::new() };
                (f.symbol, f.original, args, changed)
            };
            let rebuilt = if !changed {
                original
            } else if matches!(sig.symbol(symbol).theory(), Theory::S) {
                // An S node's `count` is non-child state `rebuild` cannot recover (it would re-wrap as
                // `s^1`); preserve the original count and re-seat it over the reduced argument.
                let count = match &self.node(original).term {
                    NodeTerm::S { count, .. } => count.clone(),
                    _ => unreachable!("a Theory::S node is NodeTerm::S"),
                };
                self.make_s(sig, symbol, count, args[0])
            } else {
                self.rebuild(sig, symbol, args)
            };

            // Phase 2: rewrite the top while an equation applies, re-reducing each result by reusing
            // this frame's slot for the rewritten term.
            if let Some(next) = self.try_rewrite_top(sig, rebuilt, &stack) {
                self.rewrite_count += 1;
                // Faithful `set trace whole`: reconstruct the whole root term before/after this top
                // rewrite (the redex `rebuilt` / result `next` threaded up through the ancestor frames)
                // and patch the just-recorded `Rewrite` event. Gated — off by default; only allocates
                // when whole-tracing is on.
                if self.record_whole && self.tracing() {
                    let before = self.reconstruct_whole(sig, &stack, rebuilt);
                    let after = self.reconstruct_whole(sig, &stack, next);
                    self.patch_whole(before, after);
                }
                // Reuse this frame's slot for the rewritten term, but carry `start` over: this frame's
                // forwarding target is still the node it was originally pushed for, not the intermediate
                // redex `rebuilt` (which is abandoned and, being unshared, needs no memo of its own).
                let start = stack.last().expect("empty reduce stack").start;
                let mut frame = self.new_reduce_frame(next);
                frame.start = start;
                *stack.last_mut().expect("empty reduce stack") = frame;
                continue;
            }

            // C1 normal-form point (Maude's `DagNode::reduce` → `fastComputeTrueSort`): `rebuilt`'s
            // equations are exhausted, so now — and only now — refine its true sort by the memberships.
            // Recompute the base sort first: a child refined in place at *its* normal-form point does
            // not propagate to this node when it was not rebuilt (`args == orig` kept `original`), so we
            // must recompute from the now-refined children before constraining. Gated on the module
            // having any `mb`/`cmb` — else the base sort never changes and `fib`/the prelude keep exactly
            // today's hot path (base sort at construction, no normal-form step, no per-rewrite cost).
            if !sig.memberships.is_empty() {
                let base = self.compute_base_sort(sig, rebuilt);
                self.dags.get_mut(rebuilt).sort = base;
                // For `set trace whole`: snapshot the whole root with `rebuilt` threaded up the ancestor
                // frames (a membership changes only its sort, not the structure) so each application can
                // render Maude's `Whole:` line. Gated — allocates O(depth) only when whole-tracing.
                let whole = (self.record_whole && self.tracing())
                    .then(|| self.reconstruct_whole(sig, &stack, rebuilt));
                self.constrain_to_smaller_sort(sig, rebuilt, whole, &stack);
            }
            // `rebuilt` is a normal form: stamp it canonical (its own nf) and hand it up. If the frame's
            // `start` node differs — it rewrote and/or its children changed — record `rebuilt` as
            // `start`'s normal form too, so a *shared* reference to `start` (under C7 construction dedup)
            // forwards straight to `rebuilt` instead of re-reducing it. Always clearing `rebuilt.nf` (not
            // just on a fresh node) guards against a stale `Some` from an earlier epoch: `start == rebuilt`
            // (a self-normal node, e.g. a constant refined by a membership) leaves `nf = None`.
            let start = stack.last().expect("empty reduce stack").start;
            {
                let n = self.dags.get_mut(rebuilt);
                n.nf = None;
                n.reduced_epoch = sig.eq_epoch();
            }
            if start != rebuilt {
                let n = self.dags.get_mut(start);
                n.nf = Some(rebuilt);
                n.reduced_epoch = sig.eq_epoch();
            }
            stack.pop();
            if stack.is_empty() {
                return rebuilt;
            }
            child_result = Some(rebuilt);
        }
    }

    /// Build a fresh [`ReduceFrame`] positioned at the start of `id`'s children. `start` defaults to
    /// `id`; the Phase-2 rewrite-replace copies the prior frame's `start` over so it survives a chain
    /// of rewrites (C7 forwarding).
    fn new_reduce_frame(&self, id: DagId) -> ReduceFrame {
        let node = self.node(id);
        let orig: Vec<DagId> = node.children().collect();
        ReduceFrame {
            start: id,
            original: id,
            symbol: node.symbol(),
            args: orig.clone(),
            orig,
            cursor: 0,
        }
    }

    /// Reconstruct the whole root term with `leaf` threaded up through the ancestor reduce frames — the
    /// in-progress whole term Maude's `root()` would show for `set trace whole`. The deepest frame
    /// (`stack.last`) is the one being rewritten (its node is `leaf`); each shallower frame contributes
    /// its symbol + current `args`, with the position it is mid-reducing (`strat_position`) replaced by
    /// the threaded child. Already-reduced siblings sit in `args`; not-yet-visited ones keep their
    /// originals — exactly the partially-normalized whole term. Allocates O(depth) nodes, so it is only
    /// called when whole-tracing is on.
    fn reconstruct_whole(&mut self, sig: &Signature, stack: &[ReduceFrame], leaf: DagId) -> DagId {
        let mut node = leaf;
        for frame in stack[..stack.len() - 1].iter().rev() {
            let pos = sig
                .strat_position(frame.symbol, frame.cursor, frame.orig.len())
                .expect("an ancestor reduce frame is mid-strategy");
            let mut args = frame.args.clone();
            args[pos] = node;
            // Preserve an S node's `count` (as the reduce loop does), else `rebuild` would re-wrap `s^1`.
            node = if matches!(sig.symbol(frame.symbol).theory(), Theory::S) {
                let count = match &self.node(frame.original).term {
                    NodeTerm::S { count, .. } => count.clone(),
                    _ => unreachable!("a Theory::S frame is over an S node"),
                };
                self.make_s(sig, frame.symbol, count, args[0])
            } else {
                self.rebuild(sig, frame.symbol, args)
            };
        }
        node
    }

    /// Attach reconstructed whole-before/after terms to the most-recently recorded `Rewrite` event (the
    /// top rewrite `try_equations`/`try_special` just recorded).
    fn patch_whole(&mut self, before: DagId, after: DagId) {
        if let Some(TraceEvent::Rewrite { whole_before, whole_after, .. }) =
            self.trace.as_mut().and_then(|b| b.last_mut())
        {
            *whole_before = Some(before);
            *whole_after = Some(after);
        }
    }

    /// Apply the first matching equation at the top of `id`, returning the instantiated rhs (or
    /// `None` if no equation applies).
    ///
    /// Driven as a **solution stream** through the A3 matcher seam: each equation's compiled
    /// [`LhsAutomaton`] yields a [`Subproblem`](crate::theory::Subproblem) whose `next` enumerates
    /// solutions into `subst`. Phase 1 equations are unconditional, so the *first* solution of the
    /// first matching equation wins; the `while sp.next(..)` loop is where a conditional equation will
    /// evaluate its condition and, on failure, fall through to the next solution — and where an AC
    /// subproblem will surface its several solutions. (Free matching yields exactly one.)
    ///
    /// The A4 borrow split is what lets this avoid cloning the rhs: `eqs` (and thus `&eq.rhs`) is a
    /// shared borrow of `sig`, disjoint from the `&mut self` runtime, so the matched rhs is
    /// instantiated straight out of the still-borrowed equation table.
    /// Whether the [`TraceEvent`] stream is being recorded (opt-in via [`Engine::set_trace`]).
    fn tracing(&self) -> bool {
        self.trace.is_some()
    }

    /// Push a trace event when tracing is on (a cheap `None` check otherwise).
    fn record(&mut self, ev: TraceEvent) {
        if let Some(buf) = &mut self.trace {
            buf.push(ev);
        }
    }

    /// Snapshot all bindings of `subst` (each `Some`/`None`) for a trace event — the statement's
    /// variables `0..nr_vars`, in index order (Maude prints them so, `(unbound)` for `None`).
    fn snapshot_subst(subst: &Subst) -> Vec<Option<DagId>> {
        (0..subst.len()).map(|i| subst.get(i)).collect()
    }

    fn try_rewrite_top(&mut self, sig: &Signature, id: DagId, frames: &[ReduceFrame]) -> Option<DagId> {
        let symbol = self.node(id).symbol();
        // Built-in operators (`special`) are the symbol's primary reduction rule (Maude's `eqRewrite`);
        // they are tried before user equations and fall through (`None`) on no-match. The `&SpecialOp`
        // borrowed from `sig` coexists with `&mut self` (the A4 split).
        if let Some(op) = sig.symbol(symbol).special()
            && let Some(r) = self.try_special(sig, id, op)
        {
            if self.tracing() {
                let depth = self.condition_depth;
                self.record(TraceEvent::Rewrite {
                    kind: RewriteKind::BuiltIn,
                    eq_id: None,
                    depth,
                    redex: id,
                    result: r,
                    bindings: Vec::new(),
                    whole_before: None,
                    whole_after: None,
                });
            }
            return Some(r);
        }
        // ACU/AU/S rewriting matches *modulo* the axioms with extension: a pattern may match a
        // sub-multiset (ACU), a contiguous sub-sequence (AU), or a successor prefix `s^k` of an `s^n`
        // subject (S), leaving a residue to splice back. The free/CUI theories match the whole node.
        let ext_allowed = matches!(sig.symbol(symbol).theory(), Theory::Acu | Theory::Au | Theory::S);
        let eqs = sig.equations.get(&symbol)?;
        // Non-owise equations first; an `[owise]` equation applies only if no non-owise one does
        // (Maude's two-phase `applyReplaceNoOwise` / `applyReplace`, B2.3b). The second pass is reached
        // only when the first found nothing — for a node with no equations the early `?` above skips both.
        // Equation rewrites (and the conditional trial/fragment events) are recorded inside
        // `try_equations`, where the eq id + substitution are in scope.
        if let Some(r) = self.try_equations(sig, id, eqs, ext_allowed, false, frames) {
            return Some(r);
        }
        self.try_equations(sig, id, eqs, ext_allowed, true, frames)
    }

    /// Try the equations of one phase (`owise == false` → the normal equations; `owise == true` → the
    /// `[owise]` fallbacks) against `id`, returning the first applicable rewrite. Drives each equation
    /// as a **solution stream** through the A3 matcher seam: the compiled [`LhsAutomaton`] yields a
    /// [`Subproblem`](crate::theory::Subproblem) whose `next` enumerates solutions into `subst`; a
    /// conditional equation accepts a solution only if its condition holds, else backtracks into the
    /// next solution (Maude's `solveCondition` retry). The A4 borrow split lets the matched `&eq.rhs`
    /// (a shared borrow of `sig`) instantiate in place without a defensive clone.
    fn try_equations(
        &mut self,
        sig: &Signature,
        id: DagId,
        eqs: &[CompiledEquation],
        ext_allowed: bool,
        owise: bool,
        frames: &[ReduceFrame],
    ) -> Option<DagId> {
        let mut subst = Subst::new();
        for eq in eqs {
            if eq.owise != owise {
                continue; // wrong phase
            }
            // First applicable solution wins (`Flow::Stop`): equational reduction takes the first
            // equation whose lhs matches and whose condition holds.
            let r = self.drive_match(
                sig,
                id,
                &eq.lhs,
                eq.nr_vars,
                &eq.condition,
                &eq.rhs,
                eq.rhs_shares,
                ext_allowed,
                &mut subst,
                StmtCtx { kind: StmtKind::Equation, stmt_id: eq.id, frames, redex: id },
                &mut |_, _| Flow::Stop,
            );
            if r.is_some() {
                return r;
            }
        }
        None
    }

    /// Drive one statement — an equation or a rule — against `subject` as a **solution stream**, the
    /// de-duplicated core of [`try_equations`](Self::try_equations) and the rule appliers
    /// ([`apply_first_rule_at`](Self::apply_first_rule_at)/[`all_successors_at`](Self::all_successors_at)).
    ///
    /// The compiled [`LhsAutomaton`] yields a [`Subproblem`](crate::theory::Subproblem) whose `next`
    /// enumerates solutions into `subst`; each solution is a *trial* — if `condition` holds (a failure
    /// backtracks into the next solution, Maude's `solveCondition` retry), the rhs is built (inside the
    /// C7 dedup window when `rhs_shares`) and spliced into the matched position by `build_result` (a
    /// whole match = just the rhs; an extension match re-assembles the theory residue — Maude's
    /// `partialConstruct`), then handed to `accept`. `accept` returns [`Flow::Stop`] to halt with that
    /// result (first-applicable: equational reduce / `rewrite` / `frewrite`) or [`Flow::Continue`] to
    /// enumerate every solution (search successor collection). Returns the first `Stop`'s result, else
    /// `None`. The caller owns `subst` (reset here to `nr_vars`) so its capacity is reused across a
    /// symbol's statements. The A4 borrow split lets the matched `&rhs` (a shared borrow of `sig`)
    /// instantiate in place without a defensive clone.
    #[allow(clippy::too_many_arguments)]
    fn drive_match(
        &mut self,
        sig: &Signature,
        subject: DagId,
        lhs: &LhsAutomaton,
        nr_vars: u32,
        condition: &[CompiledFragment],
        rhs: &Term,
        rhs_shares: bool,
        ext_allowed: bool,
        subst: &mut Subst,
        ctx: StmtCtx<'_>,
        accept: &mut dyn FnMut(&mut Runtime, DagId) -> Flow,
    ) -> Option<DagId> {
        subst.reset(nr_vars);
        let mut sp = lhs.match_(self, sig, subject, subst, ext_allowed)?;
        let rewrite_kind = match ctx.kind {
            StmtKind::Equation => RewriteKind::Equation,
            StmtKind::Rule => RewriteKind::Rule,
            StmtKind::Membership => unreachable!("memberships are not driven through drive_match"),
        };
        while sp.next(self, sig, subst) {
            // Conditional statements: each matcher solution is a *trial* — evaluate the condition, and on
            // failure backtrack into the next solution. Unconditional statements short-circuit (no call)
            // — the free reduce hot path.
            if !condition.is_empty() {
                let depth = self.condition_depth;
                if self.tracing() {
                    let bindings = Self::snapshot_subst(subst);
                    self.record(TraceEvent::TrialStart {
                        kind: ctx.kind,
                        stmt_id: ctx.stmt_id,
                        depth,
                        bindings,
                    });
                }
                let holds =
                    self.condition_holds(sig, condition, subst, ctx.kind, ctx.stmt_id, ctx.frames, ctx.redex);
                if self.tracing() {
                    self.record(TraceEvent::TrialEnd { kind: ctx.kind, depth, success: holds });
                }
                if !holds {
                    continue;
                }
            }
            // C7: an rhs with a repeated compound subterm (e.g. `< g(X), g(X) >`) is built inside a dedup
            // window so the duplicate becomes one shared node — reduced once, like Maude's CSE'd
            // `RhsBuilder`. The flag keeps the non-sharing common case (e.g. `fib`'s rhs) on the plain
            // path. Save/restore the outer `dedup` (`None` during reduce, but a nested rhs build could
            // re-enter) so the window is exactly this instantiate.
            let built = if rhs_shares {
                let saved = self.dedup.replace(HashMap::new());
                let r = self.instantiate(sig, rhs, subst);
                self.dedup = saved;
                r
            } else {
                self.instantiate(sig, rhs, subst)
            };
            let result = sp.build_result(self, sig, built);
            if self.tracing() {
                let depth = self.condition_depth;
                let bindings = Self::snapshot_subst(subst);
                self.record(TraceEvent::Rewrite {
                    kind: rewrite_kind,
                    eq_id: Some(ctx.stmt_id),
                    depth,
                    redex: ctx.redex,
                    result,
                    bindings,
                    whole_before: None,
                    whole_after: None,
                });
            }
            match accept(self, result) {
                Flow::Stop => return Some(result),
                Flow::Continue => {}
            }
        }
        None
    }

    /// Apply the first applicable rule at `node` (Pillar A): round-robin over the node's symbol's rules
    /// from `cursors`, returning `(rule_id, result)` — the rewritten node — or `None` if no rule applies.
    /// Round-robin fairness (Maude's `RuleTable::applyRules`/`nextRule`): the cursor advances **past** the
    /// rule that fired, so repeatedly rewriting a symbol cycles through its rules. Each application bumps
    /// the global `rewrite_count` (it counts toward Maude's `rewrites:` total). Reuses the shared
    /// [`drive_match`](Self::drive_match) seam, so a `crl`'s condition is checked identically to a `ceq`'s.
    fn apply_first_rule_at(
        &mut self,
        sig: &Signature,
        node: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Option<(u32, DagId)> {
        let symbol = self.node(node).symbol();
        let rules = sig.rules.get(&symbol)?;
        let n = rules.len();
        if n == 0 {
            return None;
        }
        // Rules of ACU/AU/S symbols match *modulo* the axioms with extension (a sub-multiset / contiguous
        // sub-sequence / successor prefix), exactly as equations do (try_rewrite_top).
        let ext_allowed = matches!(sig.symbol(symbol).theory(), Theory::Acu | Theory::Au | Theory::S);
        let start = (*cursors.get(&symbol).unwrap_or(&0) as usize) % n;
        let mut subst = Subst::new();
        for k in 0..n {
            let idx = (start + k) % n;
            let rule = &rules[idx];
            // Rule application happens outside `reduce`, so there are no outer reduce frames to root for a
            // conditional rule's re-entrant condition reduction; the caller keeps the whole term rooted
            // (and the REPL runs with GC off), so an empty frame slice is correct here.
            let r = self.drive_match(
                sig,
                node,
                &rule.lhs,
                rule.nr_vars,
                &rule.condition,
                &rule.rhs,
                rule.rhs_shares,
                ext_allowed,
                &mut subst,
                StmtCtx { kind: StmtKind::Rule, stmt_id: rule.id, frames: &[], redex: node },
                &mut |_, _| Flow::Stop,
            );
            if let Some(result) = r {
                let rule_id = rule.id;
                self.rewrite_count += 1;
                cursors.insert(symbol, ((idx + 1) % n) as u32);
                return Some((rule_id, result));
            }
        }
        None
    }

    /// Find the top-down-first rewritable position of `root` and apply one rule there, returning the new
    /// root (path rebuilt) or `None` if no rule applies anywhere (a normal form, for `rewrite`). Faithful
    /// to Maude's `ruleRewrite` redex-stack traversal (`Core/run.cc:24`): breadth-first from the root,
    /// trying each position in stack order; the first position whose symbol has an applicable rule
    /// rewrites, then the path back to the root is rebuilt (Maude's `copyWithReplacement`).
    fn rewrite_step(
        &mut self,
        sig: &Signature,
        root: DagId,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> Option<DagId> {
        let mut stack = vec![RedexPos { node: root, parent: usize::MAX, arg_index: 0 }];
        let mut next_to_explore = 0usize;
        let mut i = 0usize;
        loop {
            if i == stack.len() {
                // No pending position at the current frontier — stack the next node's children, skipping
                // childless leaves, until the stack grows or every node has been explored.
                loop {
                    if next_to_explore == stack.len() {
                        return None; // every position explored; no rule applies (a normal form)
                    }
                    let parent_idx = next_to_explore;
                    let d = stack[parent_idx].node;
                    let before = stack.len();
                    let children: Vec<DagId> = self.node(d).children().collect();
                    for (ai, c) in children.into_iter().enumerate() {
                        stack.push(RedexPos { node: c, parent: parent_idx, arg_index: ai });
                    }
                    next_to_explore += 1;
                    if stack.len() > before {
                        break; // grew the stack — new positions to try
                    }
                }
            }
            let node = stack[i].node;
            // A `counter` redex fires like a rule at this (top-down-first) position.
            if let Some(result) = self.try_counter(sig, node) {
                return Some(self.rebuild_path(sig, &stack, i, result));
            }
            if let Some((_rule_id, result)) = self.apply_first_rule_at(sig, node, cursors) {
                return Some(self.rebuild_path(sig, &stack, i, result));
            }
            i += 1;
        }
    }

    /// Rebuild the path from a rewritten position up to the root: starting at stack position `leaf_idx`
    /// with `new_node` in place, reconstruct each ancestor with the one argument leading to the redex
    /// replaced (Maude's chained `copyWithReplacement`). Ancestors' other children stay shared.
    fn rebuild_path(&mut self, sig: &Signature, stack: &[RedexPos], leaf_idx: usize, new_node: DagId) -> DagId {
        let mut node = new_node;
        let mut idx = leaf_idx;
        while stack[idx].parent != usize::MAX {
            let parent_idx = stack[idx].parent;
            let arg_index = stack[idx].arg_index;
            let parent_node = stack[parent_idx].node;
            let symbol = self.node(parent_node).symbol();
            let mut args: Vec<DagId> = self.node(parent_node).children().collect();
            args[arg_index] = node;
            node = self.rebuild(sig, symbol, args);
            idx = parent_idx;
        }
        node
    }

    /// Collect **every** one-step successor of `root` (Pillar A-iv `search`): each `(rule_id, term)` where
    /// some rule, at some non-frozen position, rewrites `root` to `term` (path rebuilt to the root). Every
    /// successor counts as one rewrite (Maude's search statistic). Unlike [`rewrite_step`](Self::rewrite_step)
    /// (first applicable), this enumerates all rules × all matcher solutions at all positions.
    fn state_successors(&mut self, sig: &Signature, root: DagId, out: &mut Vec<(u32, DagId)>) {
        // Enumerate all non-frozen positions (a flattened parent/arg-index list for the path rebuild).
        let mut positions = vec![RedexPos { node: root, parent: usize::MAX, arg_index: 0 }];
        let mut i = 0;
        while i < positions.len() {
            let node = positions[i].node;
            let symbol = self.node(node).symbol();
            let children: Vec<DagId> = self.node(node).children().collect();
            for (ai, c) in children.into_iter().enumerate() {
                if !sig.symbol(symbol).is_frozen_arg(ai) {
                    positions.push(RedexPos { node: c, parent: i, arg_index: ai });
                }
            }
            i += 1;
        }
        // At each position, collect every (rule, result), splicing the result back to the root.
        for pos_idx in 0..positions.len() {
            let node = positions[pos_idx].node;
            let mut local: Vec<(u32, DagId)> = Vec::new();
            self.all_successors_at(sig, node, &mut local);
            for (rule_id, result) in local {
                let spliced = self.rebuild_path(sig, &positions, pos_idx, result);
                out.push((rule_id, spliced));
            }
        }
    }

    /// Every `(rule_id, result)` of applying any of `node`'s symbol's rules (every matcher solution) at
    /// `node` itself — the per-node enumerator behind [`state_successors`](Self::state_successors). Each
    /// accepted result bumps the rewrite count.
    fn all_successors_at(&mut self, sig: &Signature, node: DagId, out: &mut Vec<(u32, DagId)>) {
        let symbol = self.node(node).symbol();
        let Some(rules) = sig.rules.get(&symbol) else {
            return;
        };
        let ext_allowed = matches!(sig.symbol(symbol).theory(), Theory::Acu | Theory::Au | Theory::S);
        let mut subst = Subst::new();
        for rule in rules {
            let rid = rule.id;
            self.drive_match(
                sig,
                node,
                &rule.lhs,
                rule.nr_vars,
                &rule.condition,
                &rule.rhs,
                rule.rhs_shares,
                ext_allowed,
                &mut subst,
                StmtCtx { kind: StmtKind::Rule, stmt_id: rule.id, frames: &[], redex: node },
                &mut |_rt, result| {
                    // The rewrite is counted (and the state reduced) by `reduce_successor` when the
                    // search commits this successor — so the per-state count snapshot stays interleaved.
                    out.push((rid, result));
                    Flow::Continue
                },
            );
        }
    }

    /// A structural hash of the DAG at `id`, **consistent with [`deep_equal`](Self::deep_equal)**: equal
    /// terms hash equal (the hash-cons contract for `search` states). Iterative post-order with a per-call
    /// memo (so shared subterms hash once and deep terms don't overflow). Mixes the symbol, the scalar
    /// payload `deep_equal` special-cases (S `count` / NA `value`, via [`DagNode::repr`]), and the child
    /// hashes in canonical order.
    fn dag_hash(&self, id: DagId) -> u64 {
        use crate::dag::NodeRepr;
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let mut memo: HashMap<DagId, u64> = HashMap::new();
        let mut stack: Vec<(DagId, bool)> = vec![(id, false)];
        while let Some((nid, processed)) = stack.pop() {
            if memo.contains_key(&nid) {
                continue;
            }
            let node = self.node(nid);
            if !processed {
                stack.push((nid, true));
                for c in node.children() {
                    if !memo.contains_key(&c) {
                        stack.push((c, false));
                    }
                }
            } else {
                let mut h = DefaultHasher::new();
                node.symbol().hash(&mut h);
                match node.repr() {
                    NodeRepr::App => {}
                    NodeRepr::Iter { count, .. } => count.hash(&mut h),
                    NodeRepr::Str(s) => s.hash(&mut h),
                    NodeRepr::Qid(q) => q.hash(&mut h),
                    NodeRepr::Float(f) => f.to_bits().hash(&mut h),
                }
                for c in node.children() {
                    memo[&c].hash(&mut h);
                }
                memo.insert(nid, h.finish());
            }
        }
        memo[&id]
    }

    /// Enumerate the solutions of matching the compiled `goal` against `state` whose `such_that` condition
    /// holds (Pillar A-iv `search` ... `such that`): one binding vector (the goal's variables `0..nr_vars`)
    /// per solution, in matcher order. `search` runs with tracing off, so the condition check records
    /// nothing (its dummy `stmt_id` is never rendered).
    fn eval_goal(
        &mut self,
        sig: &Signature,
        goal: &LhsAutomaton,
        nr_vars: u32,
        such_that: &[CompiledFragment],
        state: DagId,
    ) -> Vec<Vec<DagId>> {
        let mut solutions = Vec::new();
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let Some(mut sp) = goal.match_(self, sig, state, &mut subst, false) else {
            return solutions;
        };
        while sp.next(self, sig, &mut subst) {
            if self.condition_holds(sig, such_that, &mut subst, StmtKind::Rule, 0, &[], state) {
                solutions.push((0..nr_vars).map(|k| subst.get(k).expect("goal variable bound")).collect());
            }
        }
        solutions
    }

    /// Whether every fragment of `condition` holds under the matched substitution `subst` — the B2.3
    /// condition check the rewrite driver runs before accepting a solution (empty condition ⇒ `true`).
    ///
    /// Each fragment is evaluated by **re-entrant reduction** of its instantiated term(s). **F-2 (the
    /// engine-global active-frame root set):** that nested `reduce`'s [`safe_point_gc`](Self::safe_point_gc)
    /// only sees its *own* frame stack, so before solving we push the **outer** reduction's working set —
    /// each ancestor frame's `original` (transitively its unreduced children) and strategy-reduced `args`,
    /// the match `subst` bindings, and the `redex` — onto [`protected`](Self::protected), which
    /// `safe_point_gc` also marks (Maude marks from all active rewriting contexts). Nested conditions stack
    /// further roots; each pops its own on return. In-reduction GC therefore stays *enabled* during a
    /// condition (bounded memory — the condition's own garbage is reclaimed) without sweeping outer state.
    /// Gated on `gc_interval`: with GC off the vec is never read, so we skip the push entirely (the default
    /// REPL path is unchanged). `frames` is the outer reduce's stack; `redex` the node being rewritten/tested.
    #[allow(clippy::too_many_arguments)]
    fn condition_holds(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        subst: &mut Subst,
        kind: StmtKind,
        stmt_id: u32,
        frames: &[ReduceFrame],
        redex: DagId,
    ) -> bool {
        if condition.is_empty() {
            return true;
        }
        let restore = self.gc_interval.is_some().then(|| {
            let base = self.protected.len();
            for f in frames {
                self.protected.push(f.original);
                self.protected.push(f.start); // C7: the outer frames' memoization targets (see safe_point_gc)
                self.protected.extend_from_slice(&f.args);
            }
            for i in 0..subst.len() {
                if let Some(b) = subst.get(i) {
                    self.protected.push(b);
                }
            }
            self.protected.push(redex);
            base
        });
        let holds = self.solve_condition(sig, condition, 0, subst, kind, stmt_id);
        if let Some(base) = restore {
            self.protected.truncate(base);
        }
        holds
    }

    /// Record the end of solving condition fragment `index` (Maude's `traceEndFragment`): the fragment
    /// text again, plus — on success — the substitution after it (`Var --> binding` lines).
    fn end_fragment(&mut self, kind: StmtKind, stmt_id: u32, index: usize, depth: u32, success: bool, subst: &Subst) {
        if self.tracing() {
            let bindings = if success { Self::snapshot_subst(subst) } else { Vec::new() };
            self.record(TraceEvent::FragmentEnd {
                kind,
                stmt_id,
                index: index as u32,
                depth,
                success,
                bindings,
            });
        }
    }

    /// Trace the re-visit of a *deterministic* (equality/sort-test) fragment as the solver backtracks
    /// back through it: a succeeded deterministic fragment whose later fragments failed is re-solved by
    /// Maude's iterative `solveCondition` (and fails, having no second solution). Our recursive solver
    /// unwinds through it instead, so we reproduce just the trace events here — a `re-solving` +
    /// `failure for condition fragment` pair. **Trace-only**: it never affects the search, the rewrite
    /// count, or the bindings (a deterministic re-solve does no reduction). No-op when not tracing.
    fn trace_deterministic_backtrack(&mut self, kind: StmtKind, stmt_id: u32, i: usize, depth: u32) {
        self.record(TraceEvent::FragmentStart { kind, stmt_id, index: i as u32, depth, first_attempt: false });
        self.record(TraceEvent::FragmentEnd { kind, stmt_id, index: i as u32, depth, success: false, bindings: Vec::new() });
    }

    /// Satisfy `condition[i..]` under `subst`, backtracking (Maude's `solveCondition`): an **equality**
    /// fragment reduces both sides and compares modulo the axioms; a **sort-test** reduces the term and
    /// checks its least sort; a **matching** (`:=`) fragment reduces the subject and enumerates the
    /// pattern's solutions, recursing into the remaining fragments for each and retrying the next on
    /// failure. The re-entrant reductions are what make a condition's rewrites count toward the total.
    /// A matching fragment's `fresh_vars` are unbound before each attempt so backtracking re-binds
    /// cleanly; on overall success the accepted bindings remain in `subst` for the rhs.
    #[allow(clippy::too_many_arguments)]
    fn solve_condition(
        &mut self,
        sig: &Signature,
        condition: &[CompiledFragment],
        i: usize,
        subst: &mut Subst,
        kind: StmtKind,
        stmt_id: u32,
    ) -> bool {
        let Some(frag) = condition.get(i) else {
            return true; // every fragment satisfied
        };
        let depth = self.condition_depth;
        // Begin solving this fragment (Maude's `traceBeginFragment`, first attempt). A matching
        // fragment may re-solve on backtrack below, emitting its own `FragmentStart { first_attempt:
        // false }`.
        if self.tracing() {
            self.record(TraceEvent::FragmentStart {
                kind,
                stmt_id,
                index: i as u32,
                depth,
                first_attempt: true,
            });
        }
        // The fragment's own reduction is one condition-level deeper, so its rewrites are tagged
        // `depth + 1` (gated by `set trace condition`).
        match frag {
            CompiledFragment::Equality { lhs, rhs } => {
                // F-2: reduce each side, pinning the reduced `l` across `r`'s reduction — under
                // in-reduction GC, `l` is live only in this native local while `r` reduces, so a nested
                // safe point would otherwise sweep it. `r` is instantiated *after* `l`'s reduce, so nothing
                // unrooted is live during `l`'s reduction either.
                self.condition_depth += 1;
                let l = self.instantiate(sig, lhs, subst);
                let l = self.reduce(sig, l);
                let _root_l = self.root(l);
                let r = self.instantiate(sig, rhs, subst);
                let r = self.reduce(sig, r);
                self.condition_depth -= 1;
                let holds = self.deep_equal(l, r);
                self.end_fragment(kind, stmt_id, i, depth, holds, subst);
                if !holds {
                    return false;
                }
                if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id) {
                    return true;
                }
                // A later fragment failed: backtrack unwinds through this (succeeded) deterministic
                // fragment. Trace it as Maude does; the search/result/count are unaffected.
                self.trace_deterministic_backtrack(kind, stmt_id, i, depth);
                false
            }
            CompiledFragment::SortTest { term, sort } => {
                let t = self.instantiate(sig, term, subst);
                self.condition_depth += 1;
                let t = self.reduce(sig, t);
                self.condition_depth -= 1;
                let holds = sig.sorts().leq(self.node(t).sort, *sort);
                self.end_fragment(kind, stmt_id, i, depth, holds, subst);
                if !holds {
                    return false;
                }
                if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id) {
                    return true;
                }
                self.trace_deterministic_backtrack(kind, stmt_id, i, depth);
                false
            }
            CompiledFragment::Matching { pattern, subject, fresh_vars } => {
                let subj = self.instantiate(sig, subject, subst);
                self.condition_depth += 1;
                let subj = self.reduce(sig, subj);
                self.condition_depth -= 1;
                // F-2: `subj` — and the fresh-var bindings, which are its subterms — must survive the
                // pattern match and the recursive solve of the later fragments, both of which reduce under
                // in-reduction GC; pin it for the rest of this fragment.
                let _root_subj = self.root(subj);
                for &fv in fresh_vars {
                    subst.unbind(fv); // fresh slate, so a backtracking re-entry rebinds cleanly
                }
                let satisfied = match pattern.match_(self, sig, subj, subst, false) {
                    Some(mut sp) => {
                        let mut ok = false;
                        let mut first = true;
                        loop {
                            // A re-solve (backtrack) begins a fresh attempt (`re-solving condition
                            // fragment`); the first attempt's begin was emitted above.
                            if !first && self.tracing() {
                                self.record(TraceEvent::FragmentStart {
                                    kind,
                                    stmt_id,
                                    index: i as u32,
                                    depth,
                                    first_attempt: false,
                                });
                            }
                            first = false;
                            let found = sp.next(self, sig, subst);
                            self.end_fragment(kind, stmt_id, i, depth, found, subst);
                            if !found {
                                break; // matcher exhausted — this fragment fails
                            }
                            if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id) {
                                ok = true;
                                break;
                            }
                            // else: later fragment failed — backtrack into the next matcher solution.
                        }
                        ok
                    }
                    None => {
                        self.end_fragment(kind, stmt_id, i, depth, false, subst);
                        false
                    }
                };
                if !satisfied {
                    for &fv in fresh_vars {
                        subst.unbind(fv);
                    }
                }
                satisfied
            }
            CompiledFragment::Rewrite { lhs, pattern, fresh_vars } => {
                // Instantiate + reduce the search origin, then explore its `=>*` reachable states for a
                // matching `pattern` that lets the rest of the condition succeed (Pillar A-v).
                let start = self.instantiate(sig, lhs, subst);
                self.condition_depth += 1;
                let start = self.reduce(sig, start);
                self.condition_depth -= 1;
                self.solve_rewrite_condition(sig, start, pattern, fresh_vars, subst, condition, i, kind, stmt_id, depth)
            }
        }
    }

    /// Solve a rewrite condition `lhs => pattern` (Pillar A-v): breadth-first over the `=>*` reachable
    /// states from `start` (hash-consed by `deep_equal`; the start itself is tried first, as `=>*`
    /// includes zero steps), match `pattern` against each — binding `fresh_vars` — and recurse into the
    /// rest of the condition, backtracking to the next reachable state on failure. Every rule step counts
    /// as a rewrite (Maude accounting). Non-termination on an infinite reachable space is inherited from
    /// Maude. (The REPL runs with GC off, so the discovered states stay live; a GC-rooted variant is the
    /// same follow-up as the other re-entrant condition reductions, F-2.)
    #[allow(clippy::too_many_arguments)]
    fn solve_rewrite_condition(
        &mut self,
        sig: &Signature,
        start: DagId,
        pattern: &LhsAutomaton,
        fresh_vars: &[u32],
        subst: &mut Subst,
        condition: &[CompiledFragment],
        i: usize,
        kind: StmtKind,
        stmt_id: u32,
        depth: u32,
    ) -> bool {
        let _root = self.root(start);
        let mut seen: Vec<DagId> = vec![start];
        let mut frontier: VecDeque<DagId> = VecDeque::from([start]);
        while let Some(state) = frontier.pop_front() {
            for &fv in fresh_vars {
                subst.unbind(fv);
            }
            if let Some(mut sp) = pattern.match_(self, sig, state, subst, false) {
                while sp.next(self, sig, subst) {
                    self.end_fragment(kind, stmt_id, i, depth, true, subst);
                    if self.solve_condition(sig, condition, i + 1, subst, kind, stmt_id) {
                        return true;
                    }
                }
            }
            // Expand: every rule step is a rewrite; reduce each successor and hash-cons new states.
            let mut succs: Vec<(u32, DagId)> = Vec::new();
            self.state_successors(sig, state, &mut succs);
            for (_rule_id, succ) in succs {
                self.rewrite_count += 1;
                self.condition_depth += 1;
                let reduced = self.reduce(sig, succ);
                self.condition_depth -= 1;
                if !seen.iter().any(|&s| self.deep_equal(s, reduced)) {
                    seen.push(reduced);
                    frontier.push_back(reduced);
                }
            }
        }
        self.end_fragment(kind, stmt_id, i, depth, false, subst);
        for &fv in fresh_vars {
            subst.unbind(fv);
        }
        false
    }
}

// ======================================================================================
// Engine: the thin public facade over Signature + Runtime
// ======================================================================================

impl Engine {
    pub fn new() -> Self {
        Self::default()
    }

    /// Shared access to the immutable signature half (sorts/symbols/equations). Used by the matcher
    /// seam's tests to drive [`LhsAutomaton`](crate::theory) directly over the two halves.
    #[cfg(test)]
    pub(crate) fn signature(&self) -> &Signature {
        &self.sig
    }
    /// Shared access to the mutable runtime half (DAG arena/GC/statistics). Test-only counterpart of
    /// [`signature`](Self::signature).
    #[cfg(test)]
    pub(crate) fn runtime(&self) -> &Runtime {
        &self.rt
    }
    /// Both halves borrowed disjointly, to drive the matcher seam's `next` — which needs a `&mut
    /// Runtime` and a `&Signature` at once (the A4 split). Used by
    /// [`match_solutions`](Self::match_solutions) and its [`Solutions`] stream, and by the theory tests.
    pub(crate) fn parts_mut(&mut self) -> (&Signature, &mut Runtime) {
        (&self.sig, &mut self.rt)
    }

    // ---- sort signature ----

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        self.sig.add_sort(name)
    }
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        self.sig.add_subsort(sub, sup);
    }
    /// Finish the sort poset (compute kinds + subsort closure). Call before building DAG nodes.
    pub fn close_sorts(&mut self) {
        self.sig.close_sorts();
    }
    pub fn sorts(&self) -> &Sorts {
        self.sig.sorts()
    }

    // ---- symbols ----

    pub fn add_op(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
    ) -> SymbolId {
        self.sig.add_op(name, domain, range)
    }

    /// Attach an additional declaration to an existing operator (ad-hoc / subsort overloading); the
    /// least sort of an application is then resolved across all of them. Declarations must agree on
    /// arity and are tried in the order added (the original `add_op*` declaration stays first — the
    /// tie-break favours it). Add all declarations before building any node of `sym` (sorts cache at
    /// construction).
    pub fn add_op_decl(&mut self, sym: SymbolId, domain: Vec<SortId>, range: SortId) {
        self.sig.add_op_decl(sym, domain, range);
    }

    /// Mark an operator as a constructor (`[ctor]`, B2.4) — metadata that does not affect reduction.
    pub fn set_ctor(&mut self, sym: SymbolId) {
        self.sig.set_ctor(sym);
    }

    /// Whether every declaration of `sym` is a constructor (`[ctor]`).
    pub fn is_constructor(&self, sym: SymbolId) -> bool {
        self.sig.symbol(sym).is_constructor()
    }

    /// Set an evaluation strategy `strat (raw…)` on `sym` (B2.4): `raw` is the 1-based argument
    /// positions to reduce, in order, ending in a single `0` (reduce at top). Arguments not listed are
    /// left unreduced (lazy) — e.g. `if_then_else_fi` with `[1, 0]`.
    pub fn set_strategy(&mut self, sym: SymbolId, raw: &[u32]) {
        self.sig.set_strategy(sym, raw);
    }

    /// Mark `sym`'s frozen arguments (`frozen` / `frozen (raw…)`, Pillar A): `raw` is the 1-based frozen
    /// argument positions — pass an empty slice for a bare `[frozen]` (all arguments). A frozen argument
    /// is never rewritten by `rewrite`/`frewrite`/`search`; equational `reduce` is unaffected.
    pub fn set_frozen(&mut self, sym: SymbolId, raw: &[u32]) {
        self.sig.set_frozen(sym, raw);
    }

    /// Attach a built-in reduction rule (`special (id-hook …)`, B3) to `sym` — tried before user
    /// equations. Hook references are passed already resolved to [`SymbolId`]s (the future parser does
    /// the name resolution; hand-built modules supply them directly, as with [`add_equation`]). A
    /// [`SpecialOp::Branch`](crate::symbol::SpecialOp) auto-installs its lazy `strat (1 0)`.
    pub fn set_special(&mut self, sym: SymbolId, op: SpecialOp) {
        self.sig.set_special(sym, op);
    }

    /// Register an **ACU** operator (`assoc comm`, optionally with a two-sided `id:`). Must be binary;
    /// `identity` is the constant symbol declared as `id: <const>`, or `None`. The operator's
    /// arguments are stored flattened as a canonical multiset and matched/rewritten modulo AC(+U).
    pub fn add_op_ac(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_ac(name, domain, range, identity)
    }

    /// Register an **AU** operator (`assoc`, not commutative, optionally with a two-sided `id:`). Must
    /// be binary; arguments are stored as a flattened ordered sequence and matched modulo associativity.
    pub fn add_op_au(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_au(name, domain, range, identity)
    }

    /// Register a **CUI** operator (`comm`, not associative, optionally `idem` and/or `id:`). Must be
    /// binary; the two arguments are stored in canonical order, and `idem`/`id:` collapse `f(a,a)` /
    /// `f(a,e)` to a single element at construction.
    pub fn add_op_cui(
        &mut self,
        name: impl Into<String>,
        domain: Vec<SortId>,
        range: SortId,
        idem: bool,
        identity: Option<SymbolId>,
    ) -> SymbolId {
        self.sig.add_op_cui(name, domain, range, idem, identity)
    }

    /// Register an **S** (`iter`) operator: a unary stacked successor `s_` (Maude's `[iter]`). Must be
    /// unary; its nodes (built via [`make_iter`](Self::make_iter)) store `s^count(arg)` compactly.
    pub fn add_op_iter(&mut self, name: impl Into<String>, domain: Vec<SortId>, range: SortId) -> SymbolId {
        self.sig.add_op_iter(name, domain, range)
    }
    pub fn symbol(&self, id: SymbolId) -> &Symbol {
        self.sig.symbol(id)
    }

    // ---- DAG construction ----

    /// Build a node for `symbol` from `children`, **dispatching on the operator's theory** (free / ACU /
    /// AU / CUI / S) — the public form of the internal `rebuild`. Lets a caller (the frontend's command
    /// builder) construct a node from a symbol + already-built child DAGs without knowing the theory; the
    /// canonicalization (ACU multiset, AU flatten, S fold) happens inside. For an S (`iter`) symbol the
    /// children are one successor layer (folded into the count).
    pub fn make_node(&mut self, symbol: SymbolId, children: Vec<DagId>) -> DagId {
        self.rt.rebuild(&self.sig, symbol, children)
    }

    /// Build a free-theory node `symbol(args...)`, computing and caching its least sort.
    pub fn make_free(&mut self, symbol: SymbolId, args: Vec<DagId>) -> DagId {
        self.rt.make_free(&self.sig, symbol, args)
    }
    /// Convenience for a constant (an arity-0 symbol).
    pub fn make_const(&mut self, symbol: SymbolId) -> DagId {
        self.rt.make_const(&self.sig, symbol)
    }

    /// Build a canonical **ACU** node for an `assoc comm [id:]` operator from `(element, multiplicity)`
    /// pairs (see [`Runtime::make_acu`]). The result is in AC(+U) normal form — flattened, identity
    /// dropped, equal elements merged, canonically ordered — and may collapse to a single element or
    /// the identity. `symbol` must be ACU (declared via [`add_op_ac`](Self::add_op_ac)).
    pub fn make_acu(&mut self, symbol: SymbolId, args: Vec<(DagId, u32)>) -> DagId {
        self.rt.make_acu(&self.sig, symbol, args)
    }
    /// Convenience for [`make_acu`](Self::make_acu) from a flat list of elements (each multiplicity 1):
    /// `make_ac(plus, vec![a, b, c])` builds the canonical `a + b + c`.
    pub fn make_ac(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.rt.make_acu(&self.sig, symbol, elements.into_iter().map(|e| (e, 1)).collect())
    }

    /// Build a canonical **AU** node for an `assoc [id:]` operator from an ordered element list (see
    /// [`Runtime::make_au`]): `make_au(concat, vec![a, b, c])` builds the canonical `a b c`. Flattened
    /// and identity-dropped, order preserved; may collapse to a single element or the identity.
    pub fn make_au(&mut self, symbol: SymbolId, elements: Vec<DagId>) -> DagId {
        self.rt.make_au(&self.sig, symbol, elements)
    }

    /// Build a canonical **CUI** node for a `comm [idem] [id:]` operator from its two arguments (see
    /// [`Runtime::make_cui`]): commutatively ordered, with `f(a,a)`/`f(a,e)` collapsed.
    pub fn make_cui(&mut self, symbol: SymbolId, x: DagId, y: DagId) -> DagId {
        self.rt.make_cui(&self.sig, symbol, x, y)
    }

    /// Build a canonical **S** (`iter`) node `s^count(arg)` for an `iter` operator (see
    /// [`Runtime::make_s`]): `count == 0` collapses to `arg`, nested same-symbol successors flatten.
    /// `symbol` must be an `iter` operator (declared via [`add_op_iter`](Self::add_op_iter)).
    pub fn make_iter(&mut self, symbol: SymbolId, count: u64, arg: DagId) -> DagId {
        self.rt.make_s(&self.sig, symbol, Nat::from_u64(count), arg)
    }

    /// Build a string-literal NA node (the `<Strings>` `StringSymbol`, B3.6); `symbol` is an arity-0
    /// string-constant operator.
    pub fn make_string(&mut self, symbol: SymbolId, value: &str) -> DagId {
        self.rt.make_na(&self.sig, symbol, NaValue::Str(value.into()))
    }
    /// Build a quoted-identifier NA node (the `<Qids>` `QuotedIdentifierSymbol`, B3.6).
    pub fn make_qid(&mut self, symbol: SymbolId, value: &str) -> DagId {
        self.rt.make_na(&self.sig, symbol, NaValue::Qid(value.into()))
    }
    /// Build a float NA node (the `<Floats>` `FloatSymbol`, B3.7).
    pub fn make_float(&mut self, symbol: SymbolId, value: f64) -> DagId {
        self.rt.make_na(&self.sig, symbol, NaValue::Float(value.to_bits()))
    }

    pub fn node(&self, id: DagId) -> &DagNode {
        self.rt.node(id)
    }
    pub fn sort_of(&self, id: DagId) -> SortId {
        self.rt.sort_of(id)
    }
    /// Number of live DAG nodes (post-GC this is the reachable set).
    pub fn live_nodes(&self) -> usize {
        self.rt.live_nodes()
    }
    /// Peak DAG-arena capacity (high-water mark of allocated slots; stays bounded when GC runs).
    pub fn node_capacity(&self) -> usize {
        self.rt.node_capacity()
    }

    // ---- garbage collection (D2) ----

    /// Pin `id` as a GC root for as long as the returned [`RootGuard`] lives (decision D2 amendment).
    /// The guard registers the root on construction and releases it on `Drop`; it holds a shared
    /// handle to the registry rather than borrowing the engine, so the caller can keep it alive
    /// across `&mut self` calls like [`reduce`](Self::reduce).
    ///
    /// Bind the guard to a named local (`let _g = engine.root(id);`). `let _ = engine.root(id)` drops
    /// it immediately, releasing the root on the same line — and `#[must_use]` does *not* flag the
    /// discarding `let _` form. `id` is not validated here; a stale or cross-engine handle surfaces at
    /// the next collection, not at this call.
    pub fn root(&self, id: DagId) -> RootGuard {
        self.rt.root(id)
    }

    /// Collect every DAG node not reachable from a live [`RootGuard`] or from `extra_roots`; returns
    /// the number reclaimed. Roots pinned by guards are *always* included, so callers normally pass
    /// `[]`; `extra_roots` is the advanced entry point for roots not (yet) held by a guard — e.g. the
    /// `examples/peano` benchmark, which roots a term inline.
    pub fn gc(&mut self, extra_roots: impl IntoIterator<Item = DagId>) -> usize {
        self.rt.gc(extra_roots)
    }

    /// Enable (or disable) safe-point GC during [`reduce`](Self::reduce). `Some(interval)` collects
    /// at the reduce loop head once `interval` DAG nodes have been allocated since the last
    /// collection; `None` (default) disables it, so callers collect between reductions instead.
    ///
    /// **Rooting contract.** Once this is enabled, a collection can run *during* `reduce`. Any `DagId`
    /// you keep across a later allocation or `reduce` call — including the result of an *earlier*
    /// `reduce` — must be pinned with [`root`](Self::root), or that collection may reclaim it (it is
    /// not reachable from the in-progress reduction's working set). Using an unrooted, reclaimed
    /// handle panics in debug (the generational check) and is a silent wrong answer in release.
    pub fn set_gc_interval(&mut self, interval: Option<u64>) {
        self.rt.set_gc_interval(interval);
    }

    // ---- equations + reduction ----

    /// Register an unconditional equation, indexed by its left-hand side's top symbol. The lhs is
    /// compiled to a theory `LhsAutomaton` (the A3 matcher seam) here, once. A term canonical under
    /// the old equation set may now be reducible, so this advances the equation epoch, invalidating
    /// every node's cached "reduced" stamp (review R2 H2).
    pub fn add_equation(&mut self, eq: Equation) -> u32 {
        self.sig.add_equation(eq)
    }

    /// Register a conditional equation `ceq lhs = rhs if condition` (B2.3). The condition is a list of
    /// [`ConditionFragment`](crate::term::ConditionFragment)s (equality / sort-test); all must hold for
    /// the equation to fire, and a failed condition backtracks into the next matcher solution.
    pub fn add_conditional_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.sig.add_conditional_equation(lhs, rhs, nr_vars, condition)
    }

    /// Register an `[owise]` equation (optionally conditional): applied only when no non-owise equation
    /// of the symbol matches (B2.3b). Pass an empty `condition` for a plain `eq ... [owise]`.
    pub fn add_owise_equation(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.sig.add_owise_equation(lhs, rhs, nr_vars, condition)
    }

    /// Register an (unconditional) membership axiom `mb lhs : sort` (the lhs compiled to the A3
    /// matcher seam). Memberships lower a node's least sort at construction, so declare them before
    /// building any node of the lhs's symbol (cf. the overload add-declarations-first contract).
    pub fn add_membership(&mut self, mb: Membership) -> u32 {
        self.sig.add_membership(mb)
    }

    /// Register a conditional membership `cmb lhs : sort if condition` (B2.3c): the sort is lowered
    /// only when the condition holds under the membership match. Pass an empty `condition` for a plain
    /// `mb` (or use [`add_membership`](Self::add_membership)).
    pub fn add_conditional_membership(
        &mut self,
        lhs: Term,
        sort: SortId,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.sig.add_conditional_membership(lhs, sort, nr_vars, condition)
    }

    /// Register an unconditional rule `rl lhs => rhs` (Pillar A), returning its dense per-module id (the
    /// index the frontend keys its `rl_traces` metadata by). Rules are applied only by `rewrite`/
    /// `frewrite`/`search`, never by [`reduce`](Self::reduce).
    pub fn add_rule(&mut self, lhs: Term, rhs: Term, nr_vars: u32) -> u32 {
        self.sig.add_rule(lhs, rhs, nr_vars)
    }

    /// Register a conditional rule `crl lhs => rhs if condition` (Pillar A-iii/A-v). The condition is the
    /// same [`ConditionFragment`](crate::term::ConditionFragment) list as `ceq`, and a rule condition may
    /// additionally contain a **rewrite** fragment `t => p` (A-v).
    pub fn add_conditional_rule(
        &mut self,
        lhs: Term,
        rhs: Term,
        nr_vars: u32,
        condition: Vec<ConditionFragment>,
    ) -> u32 {
        self.sig.add_conditional_rule(lhs, rhs, nr_vars, condition)
    }

    /// Begin a `rewrite` session over `initial` (Pillar A): rule-fair, reduce-to-canonical then apply the
    /// first rule at the top-down-first redex. Returns a resumable [`Rewriting`] — drive it with
    /// [`Rewriting::run`] (bound or unbounded) and resume with `continue`. The session keeps its current
    /// term GC-rooted, so it can be stored between REPL commands.
    pub fn rewrite(&mut self, initial: DagId) -> Rewriting {
        let root = self.root(initial);
        Rewriting::new_rule_fair(root, initial)
    }

    /// One rule-fair step (used by [`Rewriting::run`]): apply the first rule at the top-down-first redex
    /// of `current`, returning the rebuilt root, or `None` at a normal form. `cursors` carries the
    /// per-symbol round-robin rule cursor across steps.
    pub(crate) fn rewrite_step(&mut self, current: DagId, cursors: &mut HashMap<SymbolId, u32>) -> Option<DagId> {
        self.rt.rewrite_step(&self.sig, current, cursors)
    }

    /// Apply the first applicable rule at `node` (round-robin via `cursors`), returning the rewritten
    /// node or `None`. Used by the position-fair `frewrite` traversal (Pillar A-ii) and `search` (A-iv),
    /// which drive the per-position rule application themselves rather than through the top-down
    /// [`rewrite_step`](Self::rewrite_step).
    pub(crate) fn rewrite_at(&mut self, node: DagId, cursors: &mut HashMap<SymbolId, u32>) -> Option<DagId> {
        self.rt.apply_first_rule_at(&self.sig, node, cursors).map(|(_, r)| r)
    }

    /// Reconstruct a node of `symbol` from `children` (the theory-aware constructor — Free/ACU/AU/CUI/S).
    /// Used by the `frewrite` traversal to rebuild a parent after rewriting a child.
    pub(crate) fn rebuild_node(&mut self, symbol: SymbolId, children: Vec<DagId>) -> DagId {
        self.rt.rebuild(&self.sig, symbol, children)
    }

    /// Begin a `search` from `initial` (Pillar A-iv): build the reachable-state graph on the fly,
    /// matching each state against `goal` (compiled here, with its `nr_vars` variables) filtered by
    /// `such_that`, for the reachability relation `arrow` up to `max_depth`. Returns a lazy
    /// [`Search`] — pull solutions with [`Search::next_solution`].
    pub fn search(
        &mut self,
        initial: DagId,
        goal: Term,
        nr_vars: u32,
        such_that: Vec<ConditionFragment>,
        arrow: Arrow,
        max_depth: Option<u32>,
    ) -> Search {
        let goal = LhsAutomaton::compile(goal, &self.sig);
        // A `such that` condition may contain a rewrite (`=>`) fragment (a nested search), so it compiles
        // with the rule owner.
        let such_that = self.sig.compile_condition(such_that, CondOwner::Rule);
        // State 0 is the reduced initial term; its reduction's rewrites count toward the search total.
        let reduced = self.reduce(initial);
        let rewrites = self.rewrites();
        let root = self.root(reduced);
        Search::new(root, reduced, rewrites, goal, nr_vars, such_that, arrow, max_depth)
    }

    /// Structural hash of the DAG at `id`, consistent with [`deep_equal`](Self::deep_equal) — the `search`
    /// state-graph hash-cons key.
    pub(crate) fn dag_hash(&self, id: DagId) -> u64 {
        self.rt.dag_hash(id)
    }

    /// Every `(rule_id, successor)` one rule step from `root` (all rules × positions) — the `search`
    /// state-expansion primitive. Successors are uncounted/unreduced; [`reduce_successor`](Self::reduce_successor)
    /// counts and canonicalizes each as the search commits it (so per-state rewrite snapshots interleave).
    pub(crate) fn state_successors(&mut self, root: DagId) -> Vec<(u32, DagId)> {
        let mut out = Vec::new();
        self.rt.state_successors(&self.sig, root, &mut out);
        out
    }

    /// Count one rule application (the search successor `succ` was just produced) and reduce it to the
    /// canonical state form. Bumping here, interleaved with the reduce, keeps each discovered state's
    /// rewrite-count snapshot faithful to Maude's incremental accounting.
    pub(crate) fn reduce_successor(&mut self, succ: DagId) -> DagId {
        self.rt.rewrite_count += 1;
        self.reduce(succ)
    }

    /// Match the compiled `goal` (filtered by `such_that`) against `state`, returning a binding vector per
    /// solution — the `search` goal test.
    pub(crate) fn eval_goal(
        &mut self,
        goal: &LhsAutomaton,
        nr_vars: u32,
        such_that: &[CompiledFragment],
        state: DagId,
    ) -> Vec<Vec<DagId>> {
        self.rt.eval_goal(&self.sig, goal, nr_vars, such_that, state)
    }

    /// Begin a `frewrite` session over `initial` (Pillar A-ii): position-fair, `gas` rule applications
    /// per position per traversal pass. Returns a resumable [`Rewriting`] (drive with [`Rewriting::run`]).
    pub fn frewrite(&mut self, initial: DagId, gas: u64) -> Rewriting {
        let root = self.root(initial);
        Rewriting::new_position_fair(root, initial, gas)
    }

    /// One position-fair traversal pass of `node` (Pillar A-ii): post-order (leaves first, left to
    /// right — a *clean*, well-defined order; see the `frewrite` divergence note in `gaps.md`), giving
    /// each **non-frozen** position up to `gas` rule applications with an equational reduce between each.
    /// `remaining` bounds the rewrites across the whole run (`None` = unbounded); `progress` records
    /// whether any rule fired (the pass loop repeats while it does). Faithful to Maude's `fairTraversal`
    /// substance — gas-bounded position fairness, reduce-between, frozen-skipping — without porting its
    /// exact redex-stack discipline (the conceded clean-order divergence affects only the intermediate
    /// term of a bounded `frewrite [n]`).
    ///
    /// Recurses on subject depth; `frewrite` is used over (shallow) configuration/object terms, and the
    /// equational reductions it calls are themselves iterative — a deep-term explicit stack is a
    /// follow-up if a pathologically deep rule structure ever appears.
    pub(crate) fn frewrite_pass(
        &mut self,
        node: DagId,
        gas: u64,
        remaining: &mut Option<u64>,
        progress: &mut bool,
        cursors: &mut HashMap<SymbolId, u32>,
    ) -> DagId {
        if *remaining == Some(0) {
            return node; // bound exhausted — leave the rest of the term as it stands
        }
        // 1. Recurse into the non-frozen children first (post-order), rebuilding the node if any changed.
        let symbol = self.node(node).symbol();
        let children: Vec<DagId> = self.node(node).children().collect();
        let mut new_children = Vec::with_capacity(children.len());
        let mut changed = false;
        for (pos, &c) in children.iter().enumerate() {
            if *remaining == Some(0) || self.symbol(symbol).is_frozen_arg(pos) {
                new_children.push(c); // frozen (rules blocked) or budget spent — keep as-is
            } else {
                let nc = self.frewrite_pass(c, gas, remaining, progress, cursors);
                changed |= nc != c;
                new_children.push(nc);
            }
        }
        let mut node = if changed { self.rebuild_node(symbol, new_children) } else { node };
        // 2. A rewritten child can enable an equation here (Maude's `ascend` reduce of a stale parent);
        //    reduce the rebuilt node to canonical form before trying rules at it. (`frozen` blocks rules,
        //    not equations, so reducing a frozen child's value is correct.)
        if changed {
            node = self.reduce(node);
        }
        // 3. Apply up to `gas` rules at this node, reducing between each (Maude's `doRewriting` gas loop).
        //    A `counter` redex fires here too (like a rule), advancing the counter.
        let mut g = gas;
        while g > 0 && *remaining != Some(0) {
            let fired = match self.rt.try_counter(&self.sig, node) {
                Some(r) => Some(r),
                None => self.rewrite_at(node, cursors),
            };
            match fired {
                Some(r) => {
                    *progress = true;
                    node = self.reduce(r);
                    g -= 1;
                    if let Some(rem) = remaining {
                        *rem -= 1;
                    }
                }
                None => break,
            }
        }
        node
    }

    /// Total equational rewrites applied so far.
    pub fn rewrites(&self) -> u64 {
        self.rt.rewrites()
    }
    pub fn reset_rewrites(&mut self) {
        self.rt.reset_rewrites();
    }
    /// Reset the `counter` built-in (Maude's `CounterSymbol`) to 0 — call at the start of each top-level
    /// `rewrite`/`frewrite` command so successive commands restart the count (`continue` does not reset).
    pub fn reset_counter(&mut self) {
        self.rt.reset_counter();
    }

    /// Enable or disable reduction tracing. When on, [`reduce`](Self::reduce) records a structured
    /// [`TraceEvent`] stream; collect it with [`take_trace`](Self::take_trace). Disabling drops any
    /// buffered events. Intended for the REPL (which runs with in-reduction GC off).
    pub fn set_trace(&mut self, on: bool) {
        self.rt.trace = on.then(Vec::new);
        self.rt.condition_depth = 0;
    }

    /// Enable/disable whole-root-term reconstruction at each rewrite (Maude's `set trace whole`). Only
    /// acts while tracing; off by default (the reconstruction allocates per rewrite). Set it alongside
    /// [`set_trace`](Self::set_trace) when rendering with the `whole` flag on.
    pub fn set_record_whole(&mut self, on: bool) {
        self.rt.record_whole = on;
    }

    /// Whether tracing is currently enabled.
    pub fn is_tracing(&self) -> bool {
        self.rt.trace.is_some()
    }

    /// Take the recorded trace events, clearing the buffer (tracing stays enabled). Empty when off.
    pub fn take_trace(&mut self) -> Vec<TraceEvent> {
        self.rt.trace.as_mut().map(std::mem::take).unwrap_or_default()
    }

    /// Open a construction-time structural-dedup window (C7): until [`end_dedup`](Self::end_dedup), DAG
    /// nodes built through the `make_*`/`rebuild`/`instantiate` funnel that are structurally identical
    /// collapse to a single shared node — so a subject like `< g(a), g(a) >` becomes one `g(a)` node,
    /// which `reduce` then normalizes once (matching Maude's hash-consed subject DAG). The frontend wraps
    /// the **subject build** (`build_dag`) in this; it must enclose a pure-construction span with no
    /// reduction or GC inside, and be balanced by `end_dedup`. Idempotent for a fresh window.
    pub fn begin_dedup(&mut self) {
        self.rt.begin_dedup();
    }

    /// Close the dedup window opened by [`begin_dedup`](Self::begin_dedup).
    pub fn end_dedup(&mut self) {
        self.rt.end_dedup();
    }

    /// Reduce `root` to canonical form by innermost, eager equational simplification. A node already
    /// stamped canonical at the current epoch is returned unchanged (forwarded to its normal form), so a
    /// *shared, already-reduced* subterm is never re-normalized. A shared subterm that is still
    /// *reducible* is normalized **once total** when the references share a DAG node (C7 forwarding +
    /// construction dedup); distinct (un-shared) occurrences are each normalized, as before.
    ///
    /// Iterative (explicit `ReduceFrame` work-stack) rather than recursive: the recursion depth of
    /// the old `reduce`/`reduce_args` grew with *subject* depth — unbounded user data — and aborted
    /// the process on deep terms (review R2 C1). This is a faithful simulation: children are reduced
    /// left-to-right before the top is rewritten, and each rewrite result is itself re-reduced, so
    /// the sequence of redexes — and thus the rewrite count — is identical to the recursive version.
    #[must_use]
    pub fn reduce(&mut self, root: DagId) -> DagId {
        self.rt.reduce(&self.sig, root)
    }

    /// Try to match pattern `pat` against `subject`, filling `subst` (which must already be
    /// [`Subst::reset`] to the pattern's variable count). Returns `true` on success; on failure
    /// `subst` may hold partial bindings, so callers reset before each attempt.
    #[must_use]
    pub fn match_pattern(&self, pat: &Term, subject: DagId, subst: &mut Subst) -> bool {
        self.rt.match_pattern(&self.sig, pat, subject, subst)
    }

    /// Structural equality of two DAG nodes (Phase 0 has no hash-consing, so this is a deep walk).
    #[must_use]
    pub fn deep_equal(&self, a: DagId, b: DagId) -> bool {
        self.rt.deep_equal(a, b)
    }

    /// Build a DAG instance of `term` under `subst` (the rhs of a matched equation).
    pub fn instantiate(&mut self, term: &Term, subst: &Subst) -> DagId {
        self.rt.instantiate(&self.sig, term, subst)
    }

    /// Begin enumerating *every* match of `pattern` (with `nr_vars` distinct variables, indexed
    /// `0..nr_vars`) against `subject` — the public face of the A3 matcher seam's multi-solution
    /// [`Subproblem`] stream, which [`match_pattern`](Self::match_pattern) (a single yes/no) cannot
    /// reach. Drives the `match`/`xmatch` commands and, later, the REPL.
    ///
    /// `extension` allows the pattern to match a *sub-part* of the subject and leave a residue (the
    /// `xmatch` command, and how AC/AU equations rewrite at the top); `false` requires the whole
    /// subject to be consumed (the plain `match` command). Returns a resumable [`Solutions`] — call
    /// [`Solutions::advance`] to step, then read [`Solutions::binding`] / [`Solutions::matched_portion`].
    pub fn match_solutions(
        &mut self,
        pattern: Term,
        nr_vars: u32,
        subject: DagId,
        extension: bool,
    ) -> Solutions<'_> {
        // Compile and run the first (deterministic) match phase. The returned `Subproblem` owns its
        // state (no borrow of the automaton or the engine), so the throwaway `automaton` can drop here
        // while the stream lives on — exactly as `try_equations` consumes it per equation.
        let automaton = LhsAutomaton::compile(pattern.clone(), &self.sig);
        let mut subst = Subst::new();
        subst.reset(nr_vars);
        let subproblem = {
            let (sig, rt) = self.parts_mut();
            automaton.match_(rt, sig, subject, &mut subst, extension)
        };
        Solutions { engine: self, pattern, subproblem, subst }
    }
}

/// A resumable stream of the matches of `pattern <=? subject`, wrapping the A3 matcher seam's
/// [`Subproblem`] so callers outside the kernel can enumerate solutions without touching the
/// crate-private matcher types. Created by [`Engine::match_solutions`].
///
/// Holds `&mut Engine` because advancing a multi-solution (ACU/AU) match allocates fresh
/// binding/residue nodes between solutions (the F-3/F-4 widening) — the same reason the reduce driver
/// drives `Subproblem::next` with `&mut Runtime`.
pub struct Solutions<'e> {
    engine: &'e mut Engine,
    /// Kept to reconstruct the matched portion (the instantiated pattern) on demand.
    pattern: Term,
    /// `None` when the subject could not match at all (no first-phase solution); then `advance` is
    /// always `false`. `Some` holds the live enumerator.
    subproblem: Option<Subproblem>,
    subst: Subst,
}

impl Solutions<'_> {
    /// Advance to the next solution, binding its variables into the internal substitution; returns
    /// `false` once the solutions are exhausted (and stays `false` thereafter). Read the solution with
    /// [`binding`](Self::binding) / [`matched_portion`](Self::matched_portion) before the next call.
    /// (Named `advance` rather than `next` — it returns a `bool` and the bound solution is read through
    /// the accessors, not yielded, so it is not an [`Iterator`].)
    #[must_use]
    pub fn advance(&mut self) -> bool {
        let Some(sp) = self.subproblem.as_mut() else { return false };
        let (sig, rt) = self.engine.parts_mut();
        sp.next(rt, sig, &mut self.subst)
    }

    /// The current solution's binding for variable `index` (`None` before the first successful
    /// [`advance`](Self::advance), or if the index is out of range).
    #[must_use]
    pub fn binding(&self, index: u32) -> Option<DagId> {
        self.subst.get(index)
    }

    /// The matched portion of the subject under the current solution — the pattern instantiated with
    /// the current bindings. For a whole (`match`) match this equals the subject; for an extension
    /// (`xmatch`) match it is the matched sub-part (the subject minus the residue). Builds a fresh
    /// node, so it takes `&mut self`; valid only after a successful [`advance`](Self::advance).
    pub fn matched_portion(&mut self) -> DagId {
        self.engine.instantiate(&self.pattern, &self.subst)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{ConditionFragment, Equation, Membership, Term};

    /// `f(a, g(a))` over a single sort `Nat`, with `a` shared (a true DAG). Returns engine + root.
    fn fixture() -> (Engine, DagId, SortId) {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        let root = e.make_free(f, vec![a1, ga]);
        (e, root, nat)
    }

    /// Decode a DAG into a sorted multiset of leaf-constant names (`b + c` → `["b","c"]`), so a public
    /// `match_solutions` binding can be compared by value.
    fn leaf_names(e: &Engine, id: DagId) -> Vec<String> {
        let node = e.node(id);
        let kids: Vec<DagId> = node.children().collect();
        if kids.is_empty() {
            vec![e.symbol(node.symbol()).name().to_string()]
        } else {
            let mut out: Vec<String> = kids.into_iter().flat_map(|c| leaf_names(e, c)).collect();
            out.sort();
            out
        }
    }

    /// The public [`Engine::match_solutions`] facade drives the ACU matcher seam end-to-end:
    /// `X + Y <=? a + b + c` enumerates the binary's six solutions (compared as a set — exact
    /// Diophantine *order* is a deferred B1 follow-up), and `xmatch a + b <=? a + b + c` yields the one
    /// extension match whose matched portion is `a + b`.
    #[test]
    fn match_solutions_enumerates_acu() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, b0, c0]);

        // `match X + Y <=? a + b + c` — whole match (no extension), six solutions. Collect the binding
        // ids while the stream is live, then decode after it drops (the caller pattern the frontend uses).
        let pat = Term::op(plus, vec![Term::var(0, s), Term::var(1, s)]);
        let mut ids: Vec<(DagId, DagId)> = Vec::new();
        {
            let mut sols = e.match_solutions(pat, 2, subject, false);
            while sols.advance() {
                ids.push((sols.binding(0).unwrap(), sols.binding(1).unwrap()));
            }
        }
        let mut got: Vec<(Vec<String>, Vec<String>)> =
            ids.iter().map(|&(x, y)| (leaf_names(&e, x), leaf_names(&e, y))).collect();
        got.sort();
        let mut want = vec![
            (vec!["a".into()], vec!["b".into(), "c".into()]),
            (vec!["b".into()], vec!["a".into(), "c".into()]),
            (vec!["c".into()], vec!["a".into(), "b".into()]),
            (vec!["a".into(), "b".into()], vec!["c".into()]),
            (vec!["a".into(), "c".into()], vec!["b".into()]),
            (vec!["b".into(), "c".into()], vec!["a".into()]),
        ];
        want.sort();
        assert_eq!(got, want, "six ACU matchers, as a set");

        // `xmatch a + b <=? a + b + c` — one extension match, matched portion `a + b`, empty subst.
        let ground = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        let portion = {
            let mut sols = e.match_solutions(ground, 0, subject, true);
            assert!(sols.advance(), "one extension solution");
            let p = sols.matched_portion();
            assert!(!sols.advance(), "exactly one");
            p
        };
        assert_eq!(leaf_names(&e, portion), vec!["a".to_string(), "b".to_string()]);
    }

    /// Three constants threaded by rules `a => b => c => d`. `rewrite` drives them to the normal form
    /// `d` in 3 rule applications, while `reduce` (which consults only the equation table) leaves `a`
    /// untouched — the structural "equations don't rewrite" guarantee (Pillar A-i).
    fn chain_engine() -> (Engine, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        e.add_rule(Term::constant(a), Term::constant(b), 0);
        e.add_rule(Term::constant(b), Term::constant(c), 0);
        e.add_rule(Term::constant(c), Term::constant(d), 0);
        (e, a, b, c, d)
    }

    #[test]
    fn rewrite_applies_rules_and_reduce_does_not() {
        let (mut e, a, _b, _c, _d) = chain_engine();

        // reduce never applies a rule: `a` is its own equational normal form.
        let a0 = e.make_const(a);
        let red = e.reduce(a0);
        assert_eq!(e.symbol(e.node(red).symbol()).name(), "a", "reduce must not apply rules");

        // rewrite drives the rules to the normal form `d` in 3 steps.
        e.reset_rewrites();
        let a1 = e.make_const(a);
        let mut rw = e.rewrite(a1);
        let step = rw.run(&mut e, None);
        assert!(step.done, "reached a normal form");
        assert_eq!(e.symbol(e.node(step.term).symbol()).name(), "d");
        assert_eq!(e.rewrites(), 3, "three rule applications");
    }

    #[test]
    fn rewrite_bound_then_continue() {
        let (mut e, a, _b, _c, _d) = chain_engine();
        let a0 = e.make_const(a);
        let mut rw = e.rewrite(a0);

        e.reset_rewrites();
        let s1 = rw.run(&mut e, Some(1));
        assert!(!s1.done, "stopped at the bound, not a normal form");
        assert_eq!(e.symbol(e.node(s1.term).symbol()).name(), "b");
        assert_eq!(e.rewrites(), 1, "exactly one rule application under [1]");

        // `continue` (unbounded) runs to the normal form, the round-robin cursor having persisted.
        let s2 = rw.run(&mut e, None);
        assert!(s2.done);
        assert_eq!(e.symbol(e.node(s2.term).symbol()).name(), "d");
    }

    #[test]
    fn gc_keeps_reachable_shared_structure() {
        let (mut e, root, _nat) = fixture();
        assert_eq!(e.live_nodes(), 3);
        assert_eq!(e.gc([root]), 0);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_collects_unreachable() {
        let (mut e, root, nat) = fixture();
        let h = e.add_op("h", vec![], nat);
        let _garbage = e.make_const(h);
        assert_eq!(e.live_nodes(), 4);
        assert_eq!(e.gc([root]), 1);
        assert_eq!(e.live_nodes(), 3);
    }

    #[test]
    fn gc_with_no_roots_collects_all() {
        let (mut e, _root, _nat) = fixture();
        assert_eq!(e.gc(Vec::new()), 3);
        assert_eq!(e.live_nodes(), 0);
    }

    #[test]
    fn computes_node_sorts_through_subsorts() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        let n0 = e.make_const(z); // 0 : Zero
        let n1 = e.make_free(s, vec![n0]); // s(0): Zero <= Nat  =>  NzNat
        let sum = e.make_free(plus, vec![n0, n1]); // Zero,NzNat <= Nat  =>  Nat

        assert_eq!(e.sort_of(n0), zero);
        assert_eq!(e.sort_of(n1), nznat);
        assert_eq!(e.sort_of(sum), nat);
    }

    /// B2.1 least sort under multi-declaration overloading (== reference binary,
    /// `conformance/overload.maude` OVERLOAD-SORT): `_+_` is overloaded `Nat Nat -> Nat` *and*
    /// `NzNat NzNat -> NzNat`; the least sort of an application is resolved across both declarations.
    #[test]
    fn overloaded_operator_least_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat); // decl 0: Nat Nat -> Nat
        e.add_op_decl(plus, vec![nznat, nznat], nznat); // decl 1: NzNat NzNat -> NzNat

        let n0 = e.make_const(z); // 0 : Zero
        let s0 = e.make_free(s, vec![n0]); // s 0 : NzNat
        assert_eq!(e.sort_of(n0), zero, "0 : Zero");
        assert_eq!(e.sort_of(s0), nznat, "s 0 : NzNat");
        // s0 / n0 are reused as shared children below (a genuine DAG share).
        let s0_plus_s0 = e.make_free(plus, vec![s0, s0]);
        assert_eq!(e.sort_of(s0_plus_s0), nznat, "s 0 + s 0 : NzNat (both args NzNat)");
        let zero_plus_s0 = e.make_free(plus, vec![n0, s0]);
        assert_eq!(e.sort_of(zero_plus_s0), nat, "0 + s 0 : Nat (Zero is not <= NzNat)");
        let zero_plus_zero = e.make_free(plus, vec![n0, n0]);
        assert_eq!(e.sort_of(zero_plus_zero), nat, "0 + 0 : Nat");
    }

    /// B2.1 (== reference binary, OVERLOAD-RED): overloading + equations — the result's least sort and
    /// the rewrite count co-vary. `s 0 + s 0` → `s s 0 : NzNat` (2 rewrites); `0 + 0` → `0 : Zero`
    /// (1 rewrite, the result re-sorts *down* from Nat to Zero).
    #[test]
    fn overloaded_operator_reduce_and_resort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_op_decl(plus, vec![nznat, nznat], nznat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let sum = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 2, "s 0 + s 0 = s s 0 in 2 rewrites");
        assert_eq!(e.sort_of(r), nznat, "result s s 0 : NzNat");
        assert_eq!(e.node(r).symbol(), s, "result is an s_ application");

        e.reset_rewrites();
        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0
        assert_eq!(e.sort_of(zz), nat, "0 + 0 : Nat before reduction");
        let r2 = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "0 + 0 = 0 in 1 rewrite");
        assert_eq!(e.sort_of(r2), zero, "result 0 : Zero (re-sorted down)");
    }

    /// B2.1 (== reference binary, OVERLOAD-ERR): no applicable declaration → the kind's error sort
    /// (and the ill-sorted term does not rewrite). Only `_+_ : NzNat NzNat -> NzNat` is declared, so
    /// `0 + 0` (Zero arguments) has no applicable declaration.
    #[test]
    fn overloaded_operator_no_applicable_decl_is_error_sort() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op("s", vec![nat], nznat);
        let plus = e.add_op("+", vec![nznat, nznat], nznat); // ONLY NzNat NzNat -> NzNat

        let (z1, z2) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(plus, vec![z1, z2]); // 0 + 0 : no decl applies
        assert!(e.sorts().sort(e.sort_of(zz)).is_error, "0 + 0 lands in the error sort");

        let z0 = e.make_const(z);
        let s0a = e.make_free(s, vec![z0]);
        let s0b = e.make_free(s, vec![z0]);
        let ss = e.make_free(plus, vec![s0a, s0b]); // s 0 + s 0 : NzNat
        assert_eq!(e.sort_of(ss), nznat, "s 0 + s 0 : NzNat (the one declaration applies)");
    }

    /// B2.1 (== reference binary, OVERLOAD-PREREG): a non-preregular operator (`f : A -> A` and
    /// `f : A -> B` with A, B incomparable) — Maude warns and assigns the least sort by the **earliest
    /// declaration**. We reproduce the tie-break (the warning itself is deferred): `f(c) : A`.
    #[test]
    fn non_preregular_overload_breaks_toward_earliest_declaration() {
        let mut e = Engine::new();
        let a = e.add_sort("A");
        let b = e.add_sort("B");
        let top = e.add_sort("Top");
        e.add_subsort(a, top);
        e.add_subsort(b, top);
        e.close_sorts();
        let c = e.add_op("c", vec![], a);
        let f = e.add_op("f", vec![a], a); // decl 0: A -> A
        e.add_op_decl(f, vec![a], b); // decl 1: A -> B (incomparable range)

        let c0 = e.make_const(c);
        let fc = e.make_free(f, vec![c0]);
        assert_eq!(e.sort_of(fc), a, "f(c) : A — the earliest of the two incomparable declarations");
    }

    /// B2.1 / audit-F-B regression (== reference binary, `conformance/acu-overload.maude` ACU-OVERLOAD):
    /// an **asymmetric** overloaded declaration on a **commutative** operator must give an
    /// argument-order-independent least sort. `_+_ : NzNat Nat -> NzNat [assoc comm]` overloaded
    /// `Nat Nat -> Nat`: `z + nz : NzNat` whichever element the canonical multiset order puts first
    /// (Maude's `commutativeSortCompletion` adds the swapped `Nat NzNat -> NzNat` declaration). The
    /// pre-fix positional fold gave `Nat` whenever the Zero element sorted first.
    #[test]
    fn acu_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let plus = e.add_op_ac("+", vec![nznat, nat], nznat, None); // decl0: NzNat Nat -> NzNat
        e.add_op_decl(plus, vec![nat, nat], nat); // decl1: Nat Nat -> Nat

        let sum = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_ac(plus, vec![x, y]);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(sum(&mut e, z, nz), "NzNat", "z + nz : NzNat (order-independent)");
        assert_eq!(sum(&mut e, nz, z), "NzNat", "nz + z : NzNat");
        assert_eq!(sum(&mut e, z, z), "Nat", "z + z : Nat");
        assert_eq!(sum(&mut e, nz, nz), "NzNat", "nz + nz : NzNat");
        // Ternary: the left-to-right multiset fold stays order-independent.
        let tern = {
            let (x, y, w) = (e.make_const(z), e.make_const(nz), e.make_const(z));
            e.make_ac(plus, vec![x, y, w])
        };
        assert_eq!(e.sorts().name(e.sort_of(tern)), "NzNat", "z + z + nz : NzNat");
    }

    /// B1/B2.1 / audit-F-B regression (== reference binary, CUI-OVERLOAD): the same order-independence
    /// for a **commutative non-associative** operator. `make_cui` orders its pair canonically (Zero
    /// before NzNat), so `g(z, nz) : NzNat` needs the swapped `Nat NzNat -> NzNat` declaration too.
    #[test]
    fn cui_asymmetric_overload_least_sort_is_commutative() {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], zero);
        let nz = e.add_op("nz", vec![], nznat);
        let g = e.add_op_cui("g", vec![nznat, nat], nznat, false, None); // NzNat Nat -> NzNat
        e.add_op_decl(g, vec![nat, nat], nat); // Nat Nat -> Nat

        let gg = |e: &mut Engine, a: SymbolId, b: SymbolId| {
            let (x, y) = (e.make_const(a), e.make_const(b));
            let s = e.make_cui(g, x, y);
            e.sorts().name(e.sort_of(s)).to_string()
        };
        assert_eq!(gg(&mut e, z, nz), "NzNat", "g(z, nz) : NzNat (order-independent)");
        assert_eq!(gg(&mut e, nz, z), "NzNat", "g(nz, z) : NzNat");
        assert_eq!(gg(&mut e, z, z), "Nat", "g(z, z) : Nat");
    }

    /// B2.2 membership axioms (== reference binary, `conformance/membership.maude` MB-PAIR): a
    /// non-linear `mb < N, N > : SymPair` lowers a pair's least sort, and **each membership application
    /// counts as a rewrite** (Maude's accounting). The lowered sort then drives which equations fire:
    /// `eq f(P) = z` with `P : SymPair` reduces `f(< z, z >)` but not `f(< z, s z >)`. Memberships are
    /// applied at construction, so each case resets the counter *before* building its query term.
    #[test]
    fn membership_lowers_sort_and_counts_as_rewrite() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let sympair = e.add_sort("SymPair");
        e.add_subsort(sympair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let f = e.add_op("f", vec![pair], nat);
        e.add_membership(Membership {
            lhs: Term::op(pairop, vec![Term::var(0, nat), Term::var(0, nat)]), // < N, N > (non-linear)
            sort: sympair,
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, sympair)]), // f(P), P : SymPair
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        // < z, z > : SymPair — one membership application. C1: construction gives the *base* sort
        // (Pair); the membership refines it to SymPair lazily, at the reduce normal-form point.
        e.reset_rewrites();
        let (z0, z1) = (e.make_const(z), e.make_const(z));
        let zz = e.make_free(pairop, vec![z0, z1]);
        assert_eq!(e.sort_of(zz), pair, "base sort Pair at construction (membership applies lazily)");
        let r = e.reduce(zz);
        assert_eq!(e.rewrites(), 1, "one membership application");
        assert_eq!(e.sort_of(r), sympair, "< z, z > : SymPair after reduce");

        // < z, s z > : Pair — components differ, no membership applies.
        e.reset_rewrites();
        let zc = e.make_const(z);
        let sz = {
            let z2 = e.make_const(z);
            e.make_free(s, vec![z2])
        };
        let zsz = e.make_free(pairop, vec![zc, sz]);
        assert_eq!(e.sort_of(zsz), pair, "< z, s z > : Pair");
        let _ = e.reduce(zsz);
        assert_eq!(e.rewrites(), 0, "no membership applies");

        // f(< z, z >) : Nat — membership (1) + equation (1) = 2 rewrites.
        e.reset_rewrites();
        let (z3, z4) = (e.make_const(z), e.make_const(z));
        let zz2 = e.make_free(pairop, vec![z3, z4]); // membership fires here
        let fzz = e.make_free(f, vec![zz2]);
        let r2 = e.reduce(fzz); // equation fires here
        assert_eq!(e.rewrites(), 2, "membership + equation");
        assert_eq!(e.node(r2).symbol(), z, "f(< z, z >) = z");

        // f(< z, s z >) : Nat — arg is only Pair, so f(P : SymPair) does not match.
        e.reset_rewrites();
        let zc2 = e.make_const(z);
        let sz2 = {
            let z5 = e.make_const(z);
            e.make_free(s, vec![z5])
        };
        let zsz2 = e.make_free(pairop, vec![zc2, sz2]);
        let fzsz = e.make_free(f, vec![zsz2]);
        let r3 = e.reduce(fzsz);
        assert_eq!(e.rewrites(), 0, "no membership, no equation");
        assert_eq!(e.node(r3).symbol(), f, "f(< z, s z >) is its own normal form");
    }

    /// B2.2 (== reference binary, MB-CHAIN): two memberships lower a sort two levels. The constrain
    /// pass is **smallest-target-sort first**, so `g(g(a))` drops straight to C (one application on the
    /// outer node), giving 2 applications total (inner `g(a) : B`, outer `g(g(a)) : C`) — not 3.
    #[test]
    fn membership_chain_lowers_two_levels() {
        let mut e = Engine::new();
        let sa = e.add_sort("A");
        let sb = e.add_sort("B");
        let sc = e.add_sort("C");
        e.add_subsort(sc, sb);
        e.add_subsort(sb, sa);
        e.close_sorts();
        let a = e.add_op("a", vec![], sa);
        let g = e.add_op("g", vec![sa], sa);
        e.add_membership(Membership { lhs: Term::op(g, vec![Term::var(0, sa)]), sort: sb, nr_vars: 1 }); // g(X) : B
        e.add_membership(Membership {
            lhs: Term::op(g, vec![Term::op(g, vec![Term::var(0, sa)])]), // g(g(X)) : C
            sort: sc,
            nr_vars: 1,
        });

        e.reset_rewrites();
        let a0 = e.make_const(a);
        assert_eq!(e.sort_of(a0), sa, "a : A");
        let _ = e.reduce(a0);
        assert_eq!(e.rewrites(), 0);

        // C1: construction gives the base sort (A); the memberships refine it lazily at reduce.
        e.reset_rewrites();
        let a1 = e.make_const(a);
        let ga = e.make_free(g, vec![a1]);
        assert_eq!(e.sort_of(ga), sa, "g(a) base sort A at construction");
        let rga = e.reduce(ga);
        assert_eq!(e.rewrites(), 1, "one membership application g(X):B");
        assert_eq!(e.sort_of(rga), sb, "g(a) : B after reduce");

        e.reset_rewrites();
        let a2 = e.make_const(a);
        let ga2 = e.make_free(g, vec![a2]);
        let gga = e.make_free(g, vec![ga2]);
        assert_eq!(e.sort_of(gga), sa, "g(g(a)) base sort A at construction");
        let rgga = e.reduce(gga);
        assert_eq!(e.rewrites(), 2, "inner g(a):B then outer g(g(a)):C — smallest-first, 2 not 3");
        assert_eq!(e.sort_of(rgga), sc, "g(g(a)) : C after reduce");
    }

    /// Tracing (opt-in) records a [`TraceEvent::Rewrite`] per rewrite — kind, the equation `id`, its
    /// `depth` (0 at top level), the redex/result, and the matched substitution. `add(s(0), s(0))`
    /// reduces in two equation steps; `take_trace` drains them and leaves the buffer empty (tracing
    /// stays on).
    #[test]
    fn trace_records_rewrite_steps() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let add = e.add_op("add", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // eq add(0, Y) = Y .   eq add(s(X), Y) = s(add(X, Y)) .   (ids 0 and 1)
        let id_add0 =
            e.add_equation(Equation { lhs: Term::op(add, vec![Term::constant(z), v(0)]), rhs: v(0), nr_vars: 1 });
        let id_adds = e.add_equation(Equation {
            lhs: Term::op(add, vec![s_of(v(0)), v(1)]),
            rhs: s_of(Term::op(add, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        assert_eq!((id_add0, id_adds), (0, 1), "dense per-module equation ids");

        let z0 = e.make_const(z);
        let one = e.make_free(s, vec![z0]);
        let subject = e.make_free(add, vec![one, one]); // add(s(0), s(0))

        assert!(!e.is_tracing());
        e.set_trace(true);
        let result = e.reduce(subject);
        let steps = e.take_trace();

        assert_eq!(steps.len(), 2, "two equation rewrites");
        // Step 0: add(s(X),Y) fires on the whole subject, binding X and Y (2 vars).
        match &steps[0] {
            TraceEvent::Rewrite { kind, eq_id, depth, redex, bindings, whole_before, .. } => {
                assert_eq!(*kind, RewriteKind::Equation);
                assert_eq!(*eq_id, Some(id_adds));
                assert_eq!(*depth, 0);
                assert_eq!(*redex, subject, "first redex is the whole subject");
                assert_eq!(bindings.len(), 2, "X, Y bound");
                assert!(bindings.iter().all(Option::is_some));
                assert!(whole_before.is_none(), "whole off by default");
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        // Step 1: add(0,Y) fires on the inner redex, binding Y (1 var).
        match &steps[1] {
            TraceEvent::Rewrite { kind, eq_id, bindings, .. } => {
                assert_eq!(*kind, RewriteKind::Equation);
                assert_eq!(*eq_id, Some(id_add0));
                assert_eq!(bindings.len(), 1, "Y bound");
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        let z1 = e.make_const(z);
        let s1 = e.make_free(s, vec![z1]);
        let two = e.make_free(s, vec![s1]);
        assert!(e.deep_equal(result, two), "add(s(0), s(0)) = s(s(0))");
        // take_trace drained the buffer; tracing is still on.
        assert!(e.take_trace().is_empty());
        assert!(e.is_tracing());
    }

    /// Whole-term tracing (`set trace whole`): each `Rewrite` event carries the reconstructed whole root
    /// term before/after. The second (inner) rewrite's whole is the *full* term `s(add(0, s 0))` → `s s
    /// 0`, not just the inner redex `add(0, s 0)` → `s 0`.
    #[test]
    fn trace_records_whole_terms() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let add = e.add_op("add", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation { lhs: Term::op(add, vec![Term::constant(z), v(0)]), rhs: v(0), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(add, vec![s_of(v(0)), v(1)]),
            rhs: s_of(Term::op(add, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        let z0 = e.make_const(z);
        let one = e.make_free(s, vec![z0]);
        let subject = e.make_free(add, vec![one, one]); // add(s(0), s(0))

        e.set_trace(true);
        e.set_record_whole(true);
        let result = e.reduce(subject);
        let steps = e.take_trace();
        assert_eq!(steps.len(), 2);

        // Build the expected whole terms to compare structurally.
        let mk = |e: &mut Engine, n: u32| {
            let mut t = e.make_const(z);
            for _ in 0..n {
                t = e.make_free(s, vec![t]);
            }
            t
        };
        let two = mk(&mut e, 2); // s s 0
        let one_again = mk(&mut e, 1); // s 0
        // Step 1 is the inner rewrite add(0, s 0) -> s 0; its WHOLE after is s s 0 (not s 0).
        match &steps[1] {
            TraceEvent::Rewrite { redex, result: res, whole_before, whole_after, .. } => {
                assert!(e.deep_equal(*res, one_again), "inner result is s 0");
                assert!(e.deep_equal(whole_after.unwrap(), two), "whole after is s s 0");
                // whole_before is s (add(0, s 0)) — strictly larger than the redex add(0, s 0).
                assert!(!e.deep_equal(whole_before.unwrap(), *redex), "whole_before is the full term");
            }
            ev => panic!("expected Rewrite, got {ev:?}"),
        }
        assert!(e.deep_equal(result, two));
    }

    /// `ceq max(M,N)=M if M<=N=ff`. The condition `M<=N` itself reduces (re-entrant), its rewrites
    /// count, and a failed first condition backtracks to the second equation — re-reducing the
    /// condition (Maude caches nothing): `max(2,1)` is 5 rewrites, not 3.
    #[test]
    fn conditional_equation_with_equality_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let max = e.add_op("max", vec![nat, nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N .
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq max(M, N) = N if M <= N = tt .   /   ceq max(M, N) = M if M <= N = ff .
        let le_mn = || Term::op(le, vec![v(0), v(1)]);
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(1),
            2,
            vec![ConditionFragment::Equality { lhs: le_mn(), rhs: Term::constant(tt) }],
        );
        e.add_conditional_equation(
            Term::op(max, vec![v(0), v(1)]),
            v(0),
            2,
            vec![ConditionFragment::Equality { lhs: le_mn(), rhs: Term::constant(ff) }],
        );

        // max(1, 2) = 2 in 3 rewrites: condition `1<=2` reduces to tt (2), then max→N (1).
        e.reset_rewrites();
        let (n1, n2) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let m = e.make_free(max, vec![n1, n2]);
        let r = e.reduce(m);
        assert_eq!(e.rewrites(), 3, "max(1,2): condition reduce (2) + max (1)");
        assert_eq!(decode(&e, r, z, s), 2, "max(1,2) = 2");

        // max(2, 1) = 2 in 5 rewrites: first condition `2<=1`→ff fails tt (2), backtrack, second
        // condition re-reduces `2<=1`→ff (2), matches ff, then max→M (1).
        e.reset_rewrites();
        let (n2b, n1b) = (numeral(&mut e, z, s, 2), numeral(&mut e, z, s, 1));
        let m2 = e.make_free(max, vec![n2b, n1b]);
        let r2 = e.reduce(m2);
        assert_eq!(e.rewrites(), 5, "max(2,1): cond fails (2) + cond re-reduced (2) + max (1)");
        assert_eq!(decode(&e, r2, z, s), 2, "max(2,1) = 2 (backtracked to the second equation)");

        // max(0, 0) = 0 in 2 rewrites.
        e.reset_rewrites();
        let (z1, z2) = (numeral(&mut e, z, s, 0), numeral(&mut e, z, s, 0));
        let m3 = e.make_free(max, vec![z1, z2]);
        let r3 = e.reduce(m3);
        assert_eq!(e.rewrites(), 2, "max(0,0): condition reduce (1) + max (1)");
        assert_eq!(decode(&e, r3, z, s), 0, "max(0,0) = 0");
    }

    /// B2.3a conditional equation with a sort-test condition (== reference binary, CEQ-SORT):
    /// `ceq nz?(N) = s z if N : NzNat` fires only when the argument's least sort is `<= NzNat`.
    #[test]
    fn conditional_equation_with_sort_test_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let nznat = e.add_sort("NzNat");
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nznat); // s_ : Nat -> NzNat
        let nzq = e.add_op("nz?", vec![nat], nat);
        e.add_conditional_equation(
            Term::op(nzq, vec![Term::var(0, nat)]),
            Term::op(s, vec![Term::constant(z)]), // = s z
            1,
            vec![ConditionFragment::SortTest { term: Term::var(0, nat), sort: nznat }],
        );

        // nz?(s z) : the argument is NzNat → condition holds → s z, 1 rewrite.
        e.reset_rewrites();
        let s0 = {
            let z0 = e.make_const(z);
            e.make_free(s, vec![z0])
        };
        let q1 = e.make_free(nzq, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1, "condition N : NzNat holds for s z");
        assert_eq!(e.sort_of(r1), nznat, "result s z : NzNat");
        assert_eq!(e.node(r1).symbol(), s);

        // nz?(z) : z is only Nat → condition fails → no rewrite.
        e.reset_rewrites();
        let z1 = e.make_const(z);
        let q2 = e.make_free(nzq, vec![z1]);
        let r2 = e.reduce(q2);
        assert_eq!(e.rewrites(), 0, "condition N : NzNat fails for z");
        assert_eq!(e.node(r2).symbol(), nzq, "nz?(z) is its own normal form");
    }

    /// B2.3a audit-F-2 mitigation: a conditional equation whose condition reduces re-entrantly stays
    /// correct with safe-point GC enabled. GC is disabled *during* condition evaluation, so the nested
    /// reduce can't sweep the outer reduction's in-flight state; the result and rewrite count are
    /// identical to the GC-off run. (`ceq f(N) = z if g(N) = tt`, with `g(s^k z)` reducing in `k+1`.)
    #[test]
    fn conditional_reduce_is_stable_under_safe_point_gc() {
        fn run(interval: Option<u64>) -> (SymbolId, u64) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            let truth = e.add_sort("Truth");
            e.close_sorts();
            let z = e.add_op("z", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let tt = e.add_op("tt", vec![], truth);
            let g = e.add_op("g", vec![nat], truth);
            let f = e.add_op("f", vec![nat], nat);
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::op(s, vec![Term::var(0, nat)])]), // g(s N) = g(N)
                rhs: Term::op(g, vec![Term::var(0, nat)]),
                nr_vars: 1,
            });
            e.add_equation(Equation {
                lhs: Term::op(g, vec![Term::constant(z)]), // g(z) = tt
                rhs: Term::constant(tt),
                nr_vars: 0,
            });
            e.add_conditional_equation(
                Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = z if g(N) = tt
                Term::constant(z),
                1,
                vec![ConditionFragment::Equality {
                    lhs: Term::op(g, vec![Term::var(0, nat)]),
                    rhs: Term::constant(tt),
                }],
            );
            e.set_gc_interval(interval);
            let n = numeral(&mut e, z, s, 20); // condition g(20) reduces in 21 rewrites
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        }
        let off = run(None);
        let on = run(Some(4)); // aggressive collection around (not during) the condition reduce
        assert_eq!(off.1, 22, "f(20) → z in 22 rewrites (21 condition + 1 equation)");
        assert_eq!(on, off, "conditional reduce identical with safe-point GC on — F-2 mitigation holds");
    }

    /// B2.3b `owise` equations (== reference binary, `conformance/owise.maude` OWISE-EQ): an `[owise]`
    /// equation fires only when no non-owise equation of the symbol matches.
    #[test]
    fn owise_equation_applies_when_no_normal_equation_matches() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let iszero = e.add_op("iszero", vec![nat], truth);
        // eq iszero(z) = tt .   eq iszero(N) = ff [owise] .
        e.add_equation(Equation {
            lhs: Term::op(iszero, vec![Term::constant(z)]),
            rhs: Term::constant(tt),
            nr_vars: 0,
        });
        e.add_owise_equation(Term::op(iszero, vec![Term::var(0, nat)]), Term::constant(ff), 1, Vec::new());

        // iszero(z): the specific non-owise equation matches.
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let q0 = e.make_free(iszero, vec![z0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r0).symbol(), tt, "iszero(z) = tt");

        // iszero(s z): nothing else matches → owise applies.
        e.reset_rewrites();
        let s0 = {
            let z1 = e.make_const(z);
            e.make_free(s, vec![z1])
        };
        let q1 = e.make_free(iszero, vec![s0]);
        let r1 = e.reduce(q1);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(e.node(r1).symbol(), ff, "iszero(s z) = ff via owise");
    }

    /// B2.3b (== reference binary, OWISE-COND): `owise` applies even when a non-owise *conditional*
    /// equation matched structurally but its condition failed. `ceq clamp(N)=z if N<=s z=tt` /
    /// `eq clamp(N)=s z [owise]`: clamp(0)=0 (2 rw), clamp(1)=0 (3 rw), clamp(2)=s z via owise (3 rw).
    #[test]
    fn owise_applies_when_conditional_equation_condition_fails() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let clamp = e.add_op("clamp", vec![nat], nat);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // ceq clamp(N) = z if N <= s z = tt .   eq clamp(N) = s z [owise] .
        e.add_conditional_equation(
            Term::op(clamp, vec![v(0)]),
            Term::constant(z),
            1,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), s_of(Term::constant(z))]),
                rhs: Term::constant(tt),
            }],
        );
        e.add_owise_equation(Term::op(clamp, vec![v(0)]), s_of(Term::constant(z)), 1, Vec::new());

        for (input, expected, rewrites) in [(0u32, 0u32, 2u64), (1, 0, 3), (2, 1, 3)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let c = e.make_free(clamp, vec![n]);
            let r = e.reduce(c);
            assert_eq!(e.rewrites(), rewrites, "clamp({input}) rewrite count");
            assert_eq!(decode(&e, r, z, s), expected, "clamp({input}) value");
        }
    }

    /// B2.3c conditional membership (== reference binary, `conformance/cmb.maude`):
    /// `cmb < M, N > : GoodPair if M <= N = tt` lowers a pair's sort only when its condition holds —
    /// and the condition's reductions count (`<z,sz>` is 2 rewrites: condition 1 + membership 1; the
    /// failing `<sz,z>` is 1, the condition reduce alone).
    #[test]
    fn conditional_membership_lowers_sort_when_condition_holds() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let pair = e.add_sort("Pair");
        let goodpair = e.add_sort("GoodPair");
        let truth = e.add_sort("Truth");
        e.add_subsort(goodpair, pair);
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let tt = e.add_op("tt", vec![], truth);
        let _ff = e.add_op("ff", vec![], truth);
        let le = e.add_op("<=", vec![nat, nat], truth);
        let pairop = e.add_op("<_,_>", vec![nat, nat], pair);
        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: Term::op(le, vec![Term::constant(z), v(0)]),
            rhs: Term::constant(tt),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), Term::constant(z)]),
            rhs: Term::constant(_ff),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(le, vec![s_of(v(0)), s_of(v(1))]),
            rhs: Term::op(le, vec![v(0), v(1)]),
            nr_vars: 2,
        });
        // cmb < M, N > : GoodPair if M <= N = tt .
        e.add_conditional_membership(
            Term::op(pairop, vec![v(0), v(1)]),
            goodpair,
            2,
            vec![ConditionFragment::Equality {
                lhs: Term::op(le, vec![v(0), v(1)]),
                rhs: Term::constant(tt),
            }],
        );

        // Build < a, b >, reduce it, and read back its least sort + rewrite count. C1: the cmb now fires
        // at the reduce normal-form point (not construction), so we reduce before reading — the count
        // (condition reductions + the cmb application) is the same, just relocated from build to reduce.
        let build = |e: &mut Engine, a: u32, b: u32| -> (SortId, u64) {
            e.reset_rewrites();
            let na = numeral(e, z, s, a);
            let nb = numeral(e, z, s, b);
            let p = e.make_free(pairop, vec![na, nb]);
            let p = e.reduce(p);
            (e.sort_of(p), e.rewrites())
        };
        assert_eq!(build(&mut e, 0, 1), (goodpair, 2), "< z, s z > : GoodPair, 2 rewrites");
        assert_eq!(build(&mut e, 1, 0), (pair, 1), "< s z, z > : Pair (condition fails), 1 rewrite");
        assert_eq!(build(&mut e, 0, 0), (goodpair, 2), "< z, z > : GoodPair, 2 rewrites");
        assert_eq!(build(&mut e, 1, 1), (goodpair, 3), "< s z, s z > : GoodPair, 3 rewrites");
    }

    /// B2.3d matching condition `:=` (== reference binary, `conformance/match-cond.maude` MATCH-COND):
    /// `ceq pred(N) = M if s M := N` binds the fresh `M` by matching the pattern `s M` against `N`. The
    /// `:=` match itself is not a rewrite (only the rhs application is); a non-matching subject (`z`)
    /// fails the condition.
    #[test]
    fn matching_condition_binds_fresh_variable() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let pred = e.add_op("pred", vec![nat], nat);
        // ceq pred(N) = M if s M := N .   (N = var 0, M = var 1, introduced fresh by the `:=`)
        e.add_conditional_equation(
            Term::op(pred, vec![Term::var(0, nat)]),
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::var(0, nat),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(2u32, 1u32), (1, 0)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(pred, vec![n]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1, "pred({input}): one rewrite (the := match is not counted)");
            assert_eq!(decode(&e, r, z, s), expected, "pred({input}) = {expected}");
        }

        // pred(z): `s M := z` has no match → condition fails → no rewrite.
        e.reset_rewrites();
        let n0 = numeral(&mut e, z, s, 0);
        let q0 = e.make_free(pred, vec![n0]);
        let r0 = e.reduce(q0);
        assert_eq!(e.rewrites(), 0, "pred(z): the matching condition fails");
        assert_eq!(e.node(r0).symbol(), pred, "pred(z) is its own normal form");
    }

    /// B2.3d (== reference binary, MATCH-COND2): the matching subject itself reduces before the pattern
    /// is matched. `ceq f(N) = M if s M := g(N)` with `eq g(N) = s s N`: f(0)=1 and f(1)=2, each 2
    /// rewrites (g reduces once, then f→M).
    #[test]
    fn matching_condition_reduces_subject_first() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let g = e.add_op("g", vec![nat], nat);
        let f = e.add_op("f", vec![nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::var(0, nat)]), // g(N) = s s N
            rhs: Term::op(s, vec![Term::op(s, vec![Term::var(0, nat)])]),
            nr_vars: 1,
        });
        e.add_conditional_equation(
            Term::op(f, vec![Term::var(0, nat)]), // ceq f(N) = M if s M := g(N)
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::op(s, vec![Term::var(1, nat)]),
                subject: Term::op(g, vec![Term::var(0, nat)]),
                fresh_vars: vec![1],
            }],
        );

        for (input, expected) in [(0u32, 1u32), (1, 2)] {
            e.reset_rewrites();
            let n = numeral(&mut e, z, s, input);
            let q = e.make_free(f, vec![n]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 2, "f({input}): g reduces (1) + f→M (1)");
            assert_eq!(decode(&e, r, z, s), expected, "f({input}) = {expected}");
        }
    }

    /// B2.4 `[ctor]` (== reference binary): a constructor declaration is recorded but does **not**
    /// affect functional reduction — `s 0 + s s 0` is `s s s 0` in 3 rewrites either way.
    #[test]
    fn ctor_is_recorded_and_inert_for_reduction() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.set_ctor(z);
        e.set_ctor(s);
        assert!(e.is_constructor(z), "z is a constructor");
        assert!(e.is_constructor(s), "s is a constructor");
        assert!(!e.is_constructor(plus), "+ is a defined function, not a constructor");
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(z)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        let (a, b) = (numeral(&mut e, z, s, 1), numeral(&mut e, z, s, 2));
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(e.rewrites(), 3, "[ctor] does not change the rewrite count");
        assert_eq!(decode(&e, r, z, s), 3, "s 0 + s s 0 = s s s 0");
    }

    /// B2.4 evaluation strategy (== reference binary, `conformance/strat.maude`): `if_then_else_fi` with
    /// `strat (1 0)` reduces the condition then the top, leaving the unused branch unreduced. The chosen
    /// branch *is* reduced (it becomes the result), so `if tt then big else z` costs the `big` reduction
    /// while `if tt then z else big` does not.
    #[test]
    fn evaluation_strategy_is_lazy() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let truth = e.add_sort("Truth");
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("z", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let big = e.add_op("big", vec![], nat);
        let ite = e.add_op("if", vec![truth, nat, nat], nat);
        e.set_strategy(ite, &[1, 0]); // reduce arg 1 (the condition), then top; branches lazy
        let v = |i| Term::var(i, nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s z
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(tt), v(0), v(1)]), // if tt then X else Y = X
            rhs: v(0),
            nr_vars: 2,
        });
        e.add_equation(Equation {
            lhs: Term::op(ite, vec![Term::constant(ff), v(0), v(1)]), // if ff then X else Y = Y
            rhs: v(1),
            nr_vars: 2,
        });

        // big = s s z (sanity).
        e.reset_rewrites();
        let bnode = e.make_const(big);
        let rb = e.reduce(bnode);
        assert_eq!(e.rewrites(), 1);
        assert_eq!(decode(&e, rb, z, s), 2, "big = s s z");

        // Each case: build if(cond, then, else) and reduce. (cond_is_tt, then_big, expected, rewrites)
        let cases = [
            (true, false, 0u32, 1u64),  // if tt then z   else big -> z      (else not reduced)
            (false, true, 0, 1),        // if ff then big else z   -> z      (then not reduced)
            (true, true, 2, 2),         // if tt then big else z   -> s s z  (chosen big IS reduced)
        ];
        for (cond_tt, then_big, expected, rewrites) in cases {
            e.reset_rewrites();
            let cond = if cond_tt { e.make_const(tt) } else { e.make_const(ff) };
            let then_arg = if then_big { e.make_const(big) } else { e.make_const(z) };
            let else_arg = if then_big { e.make_const(z) } else { e.make_const(big) };
            let q = e.make_free(ite, vec![cond, then_arg, else_arg]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), rewrites, "rewrite count for case {cond_tt}/{then_big}");
            assert_eq!(decode(&e, r, z, s), expected, "result for case {cond_tt}/{then_big}");
        }
    }

    #[test]
    #[should_panic]
    fn arity_mismatch_panics() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let f = e.add_op("f", vec![nat, nat], nat);
        let _ = e.make_free(f, Vec::new());
    }

    /// B1.1: an `assoc comm` operator classifies as the ACU theory and carries its axioms +
    /// identity; a plain operator stays Free. (The free hot path must be untouched by AC ops.)
    #[test]
    fn ac_operator_is_classified_acu() {
        use crate::symbol::Theory;
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let empty = e.add_op("empty", vec![], nat);
        let union = e.add_op_ac("union", vec![nat, nat], nat, Some(empty));
        let plus = e.add_op("+", vec![nat, nat], nat); // a free op, for contrast

        let u = e.symbol(union);
        assert_eq!(u.theory(), Theory::Acu);
        assert_eq!(u.identity(), Some(empty));
        assert_eq!(e.symbol(plus).theory(), Theory::Free, "a plain op is free");
        assert_eq!(e.symbol(empty).theory(), Theory::Free, "a constant is free");
    }

    #[test]
    #[should_panic(expected = "must be binary")]
    fn ac_operator_must_be_binary() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let _ = e.add_op_ac("bad", vec![nat, nat, nat], nat, None);
    }

    /// Engine with constants `a`,`b`,`c` and an `assoc comm` `+` (no identity) over sort `S`.
    fn ac_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        (e, s, a, b, c, plus)
    }

    /// B1.2: ACU construction is canonical modulo commutativity and associativity — `a+b == b+a`,
    /// and `(a+b)+c == a+(b+c) == a+b+c` (flattened to a 3-element multiset).
    #[test]
    fn acu_canonical_modulo_ac() {
        let (mut e, _s, a, b, c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        };
        let ba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y])
        };
        assert!(e.deep_equal(ab, ba), "a+b == b+a");
        assert_eq!(
            e.runtime().dag_compare(ab, ba),
            std::cmp::Ordering::Equal,
            "and the total order agrees"
        );

        let abc_left = {
            // (a+b)+c — the left arg is itself an ACU node, must flatten
            let (x, y) = (e.make_const(a), e.make_const(b));
            let ab = e.make_ac(plus, vec![x, y]);
            let z = e.make_const(c);
            e.make_ac(plus, vec![ab, z])
        };
        let abc_right = {
            let (y, z) = (e.make_const(b), e.make_const(c));
            let bc = e.make_ac(plus, vec![y, z]);
            let x = e.make_const(a);
            e.make_ac(plus, vec![x, bc])
        };
        let abc_flat = {
            let (x, y, z) = (e.make_const(a), e.make_const(b), e.make_const(c));
            e.make_ac(plus, vec![x, y, z])
        };
        assert!(e.deep_equal(abc_left, abc_right), "(a+b)+c == a+(b+c)");
        assert!(e.deep_equal(abc_left, abc_flat), "(a+b)+c == a+b+c");
        assert_eq!(e.node(abc_flat).children().count(), 3, "flattened to 3 children");
    }

    /// B1.2: identity (`id:`) elements vanish and the multiset collapses — `a+e == a`, `e+e == e`,
    /// `a+e+b == a+b`.
    #[test]
    fn acu_identity_collapses() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, Some(unit));

        let a_plus_e = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_ac(plus, vec![x, u])
        };
        assert_eq!(e.node(a_plus_e).symbol(), a, "a + e collapses to a");

        let e_plus_e = {
            let (u1, u2) = (e.make_const(unit), e.make_const(unit));
            e.make_ac(plus, vec![u1, u2])
        };
        assert_eq!(e.node(e_plus_e).symbol(), unit, "e + e collapses to e");

        let aeb = {
            let (x, u, y) = (e.make_const(a), e.make_const(unit), e.make_const(b));
            e.make_ac(plus, vec![x, u, y])
        };
        assert_eq!(e.node(aeb).children().count(), 2, "a + e + b == a + b (2 children)");
    }

    /// B1.2: equal elements merge into a multiplicity (`a+a` keeps two children via one `(a,2)` pair),
    /// and a lone element never gets wrapped (`make_ac` of one element is that element).
    #[test]
    fn acu_merges_multiplicity_and_never_wraps_singleton() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let aa = {
            let (x, y) = (e.make_const(a), e.make_const(a)); // distinct ids, structurally equal
            e.make_ac(plus, vec![x, y])
        };
        assert_eq!(e.node(aa).children().count(), 2, "a + a has two children (multiplicity 2)");
        assert_eq!(e.node(aa).symbol(), plus, "a + a is an ACU node");

        let lone = e.make_const(a);
        let wrapped = e.make_ac(plus, vec![lone]);
        assert_eq!(wrapped, lone, "make_ac of a single element collapses to it");
    }

    /// B1.2: GC traces an ACU DAG through the visitor (reachable kept, rest reclaimed) and `deep_equal`
    /// is modulo-AC across *distinct* element ids.
    #[test]
    fn acu_gc_and_modulo_equality() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        let ab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_ac(plus, vec![x, y])
        }; // ab + a0 + b0 = 3 nodes
        let _garbage = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_ac(plus, vec![x, y]) // structurally equal to ab but distinct ids
        };
        assert!(e.deep_equal(ab, _garbage), "b+a == a+b across distinct ids");
        assert_eq!(e.gc([ab]), 3, "the unreachable b+a subgraph (3 nodes) is reclaimed");
        assert_eq!(e.node(ab).children().count(), 2, "ab survives intact");
    }

    #[test]
    #[should_panic(expected = "make_acu")]
    fn make_free_on_ac_operator_panics() {
        let (mut e, _s, a, _b, _c, plus) = ac_ctx();
        let a0 = e.make_const(a);
        let _ = e.make_free(plus, vec![a0, a0]); // building an ACU op as a free node is a bug
    }

    fn s_of_zero(e: &mut Engine, zero: SymbolId, s: SymbolId) -> DagId {
        let z = e.make_const(zero);
        e.make_free(s, vec![z])
    }

    /// B1.5 reduce lock (== reference binary): `op _+_ [assoc comm]`, `eq X + 0 = X`;
    /// `red s 0 + 0 + s 0 + s 0` → `s 0 + s 0 + s 0` in **1** rewrite (X absorbs the rest; the ground
    /// `0` is consumed and spliced away as residue).
    #[test]
    fn ac_reduce_ground_consumed_with_extension() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op_ac("+", vec![nat, nat], nat, None);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        let (s0a, s0b, s0c) =
            (s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s));
        let z = e.make_const(zero);
        let subject = e.make_ac(plus, vec![s0a, z, s0b, s0c]); // s0 + 0 + s0 + s0
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "one rewrite removes the 0");
        let kids: Vec<_> = e.node(r).children().collect();
        assert_eq!(kids.len(), 3, "result is s0 + s0 + s0");
        assert!(kids.iter().all(|&k| e.node(k).symbol() == s), "all three are successors");
    }

    /// B1.5 reduce lock: ground AC pattern needing a residue splice — `eq a + a = a` on `a + a + b`
    /// → `a + b` in **1** rewrite (the matched `{a,a}` is replaced by `a`, residue `b` spliced).
    #[test]
    fn ac_reduce_ground_pattern_residue_splice() {
        let (mut e, _s, a, b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::constant(a)]),
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (a0, a1, b0) = (e.make_const(a), e.make_const(a), e.make_const(b));
        let subject = e.make_ac(plus, vec![a0, a1, b0]); // a + a + b
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + a = a fires once");
        let mut kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        kids.sort_by_key(|s| format!("{s:?}"));
        assert_eq!(kids, vec![a, b], "result is a + b");
    }

    /// B1.5 reduce lock (the subtle one — non-linear AC variable + identity): `op _;_ [assoc comm
    /// id: empty]`, `eq N ; N = N`; `red 0 ; s0 ; 0 ; s0` → `0 ; s0` in **2** rewrites. Reproducing
    /// the count needs minimal-first solution order + skipping the empty (no-op) binding.
    #[test]
    fn ac_reduce_set_idempotency_two_rewrites() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let empty = e.add_op("empty", vec![], nat);
        let set = e.add_op_ac(";", vec![nat, nat], nat, Some(empty));
        e.add_equation(Equation {
            lhs: Term::op(set, vec![Term::var(0, nat), Term::var(0, nat)]), // N ; N
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        let (z0, z1) = (e.make_const(zero), e.make_const(zero));
        let (s0a, s0b) = (s_of_zero(&mut e, zero, s), s_of_zero(&mut e, zero, s));
        let subject = e.make_ac(set, vec![z0, s0a, z1, s0b]); // 0 ; s0 ; 0 ; s0
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 2, "two duplicate-removals (== reference binary)");
        assert_eq!(e.node(r).children().count(), 2, "result is 0 ; s0");
    }

    /// B1.5 reduce lock: non-linear pure-AC idempotency `eq X + X = X` on `a+a+a+a` → `a` in **3**
    /// rewrites (X binds a single `a` each step — minimal binding, not the whole half).
    #[test]
    fn ac_reduce_nonlinear_idempotency_three_rewrites() {
        let (mut e, s, a, _b, _c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, s), Term::var(0, s)]), // X + X
            rhs: Term::var(0, s),
            nr_vars: 1,
        });
        let (a0, a1, a2, a3) =
            (e.make_const(a), e.make_const(a), e.make_const(a), e.make_const(a));
        let subject = e.make_ac(plus, vec![a0, a1, a2, a3]); // a + a + a + a
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 3, "X binds a single `a` each step (== reference binary)");
        assert_eq!(e.node(r).symbol(), a, "result collapses to the constant a");
    }

    /// B1.5 reduce lock (lone-variable collector strategy, == reference binary): `eq a + X = b` on
    /// `a + c + c` → `b` in 1 rewrite. X absorbs `c + c` (a whole match), NOT a minimal binding that
    /// would leave `b + c` — the system is non-confluent under extension and Maude takes the collector
    /// match. (Regression for the latent bug where a lone linear variable bound minimally.)
    #[test]
    fn ac_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, plus) = ac_ctx();
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::constant(a), Term::var(0, s)]), // a + X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_ac(plus, vec![a0, c0, c1]); // a + c + c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a + X = b fires once");
        assert_eq!(e.node(r).symbol(), b, "result is b (X absorbed c + c), not b + c");
    }

    /// C8: a theory-rooted (AC) subterm under a *free* operator is matched via the cross-theory
    /// `Sequence` arm — the free skeleton (`f(_)`) binds, the AC alien `a + b` is matched recursively.
    /// `eq f(a + b) = cc` fires on `f(b + a)` (the `+` canonicalizes). Was a loud guard ("theory-rooted
    /// … not yet supported"); == the reference binary (`cc`, 1 rewrite).
    #[test]
    fn free_pattern_over_theory_subterm_matches() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let c = e.add_op("cc", vec![], s);
        let f = e.add_op("f", vec![s], s); // free, unary
        // eq f(a + b) = cc   — `a + b` is an AC subterm under the free `f`.
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::op(plus, vec![Term::constant(a), Term::constant(b)])]),
            rhs: Term::constant(c),
            nr_vars: 0,
        });
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let ba = e.make_ac(plus, vec![b0, a0]); // b + a  → canonical a + b
        let subject = e.make_free(f, vec![ba]); // f(b + a)
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "f(a + b) = cc fires once");
        assert_eq!(e.node(r).symbol(), c, "result is cc");
    }

    /// The guard's boundary: a *variable* over a theory subject is fine (it binds the whole AC node),
    /// so `eq f(X) = g(X)` compiles and fires on `f(a + b)`. Only a *structured* theory sub-pattern is
    /// rejected — not a variable that happens to bind a theory term.
    #[test]
    fn free_pattern_with_variable_over_theory_subject_is_allowed() {
        let (mut e, s, a, b, _c, plus) = ac_ctx();
        let g = e.add_op("g", vec![s], s);
        let f = e.add_op("f", vec![s], s);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, s)]), // f(X)
            rhs: Term::op(g, vec![Term::var(0, s)]), // g(X)
            nr_vars: 1,
        });
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let ab = e.make_ac(plus, vec![a0, b0]); // a + b
        let subject = e.make_free(f, vec![ab]); // f(a + b)
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "f(X) = g(X) fires once on f(a + b)");
        assert_eq!(e.node(r).symbol(), g, "result is g(a + b)");
    }

    /// C8: a theory-rooted subterm under a *theory* operator (an ACU `+` term as an argument of the ACU
    /// `;`) is matched as an **alien** — compiled to its own automaton and matched recursively — so
    /// `eq (a + b) ; c = d` fires on `(a + b) ; c` (and, modulo commutativity, on `(b + a) ; c`). Was a
    /// loud guard ("theory-rooted ground subterm … not yet supported"); == the reference binary (`d`, 1).
    #[test]
    fn theory_subterm_under_theory_operator_matches() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let plus = e.add_op_ac("+", vec![s, s], s, None);
        let semi = e.add_op_ac(";", vec![s, s], s, None);
        let ab = Term::op(plus, vec![Term::constant(a), Term::constant(b)]);
        e.add_equation(Equation {
            lhs: Term::op(semi, vec![ab, Term::constant(c)]),
            rhs: Term::constant(d),
            nr_vars: 0,
        });
        // Build `(b + a) ; c` (the `+` canonicalizes to `a + b`); the alien `a + b` matches it.
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let ba = e.make_ac(plus, vec![b0, a0]);
        let subject = e.make_ac(semi, vec![ba, c0]);
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "(a + b) ; c = d fires once");
        assert_eq!(e.node(r).symbol(), d, "result is d");
    }

    /// Engine with constants `a`,`b`,`c`,`d` and an `assoc` (not comm) `__` over sort `E`.
    fn au_ctx() -> (Engine, SortId, SymbolId, SymbolId, SymbolId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let d = e.add_op("d", vec![], s);
        let cat = e.add_op_au("__", vec![s, s], s, None);
        (e, s, a, b, c, d, cat)
    }

    /// B1 AU reduce lock (extension on both ends, == reference binary): `op __ [assoc]`, `eq b c = a`;
    /// `red d b c d` → `d a d` in 1 rewrite (the contiguous `b c` is matched, prefix `d` and suffix
    /// `d` are spliced back around the rhs — order preserved).
    #[test]
    fn au_reduce_ground_pattern_extension_both_ends() {
        let (mut e, _s, a, b, c, d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(b), Term::constant(c)]), // b c
            rhs: Term::constant(a),
            nr_vars: 0,
        });
        let (d0, b0, c0, d1) =
            (e.make_const(d), e.make_const(b), e.make_const(c), e.make_const(d));
        let subject = e.make_au(cat, vec![d0, b0, c0, d1]); // d b c d
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "b c = a fires once");
        let kids: Vec<_> = e.node(r).children().map(|k| e.node(k).symbol()).collect();
        assert_eq!(kids, vec![d, a, d], "result is the ordered sequence d a d");
    }

    /// B1 AU reduce lock (lone-variable collector, == reference binary): `eq a X = b` on `a c c` → `b`
    /// in 1 rewrite (X absorbs the ordered tail `c c`; not `b c` from a minimal binding).
    #[test]
    fn au_reduce_lone_variable_absorbs() {
        let (mut e, s, a, b, c, _d, cat) = au_ctx();
        e.add_equation(Equation {
            lhs: Term::op(cat, vec![Term::constant(a), Term::var(0, s)]), // a X
            rhs: Term::constant(b),
            nr_vars: 1,
        });
        let (a0, c0, c1) = (e.make_const(a), e.make_const(c), e.make_const(c));
        let subject = e.make_au(cat, vec![a0, c0, c1]); // a c c
        let r = e.reduce(subject);
        assert_eq!(e.rewrites(), 1, "a X = b fires once");
        assert_eq!(e.node(r).symbol(), b, "result is b (X absorbed c c)");
    }

    /// B1 CUI canonicalization (== reference binary): `comm` orders the pair (`f(b,a) == f(a,b)`);
    /// `idem` collapses `g(a,a)` to `a`; `id:` collapses `h(a,e)` to `a` — all at construction.
    #[test]
    fn cui_canonical_comm_idem_identity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, false, None);
        let g = e.add_op_cui("g", vec![s, s], s, true, None); // idem
        let h = e.add_op_cui("h", vec![s, s], s, false, Some(unit)); // id: e

        let fab = {
            let (x, y) = (e.make_const(a), e.make_const(b));
            e.make_cui(f, x, y)
        };
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a) → canonical f(a, b)
        };
        assert!(e.deep_equal(fab, fba), "f(a, b) == f(b, a) (comm)");

        let gaa = {
            let (x, y) = (e.make_const(a), e.make_const(a));
            e.make_cui(g, x, y)
        };
        assert_eq!(e.node(gaa).symbol(), a, "g(a, a) collapses to a (idem)");

        let hae = {
            let (x, u) = (e.make_const(a), e.make_const(unit));
            e.make_cui(h, x, u)
        };
        assert_eq!(e.node(hae).symbol(), a, "h(a, e) collapses to a (id:)");
    }

    /// B1 CUI reduce lock (== reference binary): `eq f(a, b) = c` matches `f(b, a)` modulo
    /// commutativity → `c` in 1 rewrite.
    #[test]
    fn cui_reduce_modulo_commutativity() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, false, None);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::constant(a), Term::constant(b)]), // f(a, b)
            rhs: Term::constant(c),
            nr_vars: 0,
        });
        let fba = {
            let (x, y) = (e.make_const(b), e.make_const(a));
            e.make_cui(f, x, y) // f(b, a)
        };
        let r = e.reduce(fba);
        assert_eq!(e.rewrites(), 1, "f(a,b)=c matches f(b,a) modulo comm");
        assert_eq!(e.node(r).symbol(), c, "result is c");
    }

    /// Engine with sorts `Zero NzNat < Nat`, `0 : Zero`, and a unary `iter` successor `s_ : Nat -> NzNat`.
    fn iter_ctx() -> (Engine, SortId, SortId, SortId, SymbolId, SymbolId) {
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        (e, zero, nznat, nat, z, s)
    }

    /// Build `s^n(0)` (a fresh `0` each call, so subjects don't alias).
    fn iter_num(e: &mut Engine, z: SymbolId, s: SymbolId, n: u64) -> DagId {
        let z0 = e.make_const(z);
        e.make_iter(s, n, z0)
    }

    /// Decode an `s^n(0)` numeral (or the `0` constant) back to `n`.
    fn decode_nat(e: &Engine, id: DagId) -> u64 {
        match &e.node(id).term {
            NodeTerm::S { count, .. } => count.to_usize().expect("small numeral") as u64,
            _ => 0,
        }
    }

    /// Render a rational/integer result for comparison: `"2"`, `"3/4"`, `"-3/2"`, `"0/5"`.
    fn rat_str(e: &Engine, minus: SymbolId, div: SymbolId, id: DagId) -> String {
        let int_str = |i: DagId| match &e.node(i).term {
            NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                format!("-{}", decode_nat(e, args[0]))
            }
            _ => decode_nat(e, i).to_string(),
        };
        match &e.node(id).term {
            NodeTerm::Free { symbol, args } if *symbol == div && args.len() == 2 => {
                format!("{}/{}", int_str(args[0]), int_str(args[1]))
            }
            _ => int_str(id),
        }
    }

    /// B3.2 S-theory construction + sort (== reference binary, `conformance/iter.maude` ITER): `s^n(0)`
    /// stores the count compactly, `s^0(x)` collapses to `x`, nested successors flatten, and the sort
    /// follows the successor's declaration (`s^n(0) : NzNat` for n >= 1, `0 : Zero`).
    #[test]
    fn iter_node_construction_and_sort() {
        let (mut e, zero, nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        assert_eq!(e.sort_of(z0), zero, "0 : Zero");
        let s1 = e.make_iter(s, 1, z0);
        assert_eq!(e.sort_of(s1), nznat, "s 0 : NzNat");
        let s5 = e.make_iter(s, 5, z0);
        assert_eq!(e.sort_of(s5), nznat, "s^5 0 : NzNat");

        let collapse = e.make_iter(s, 0, z0);
        assert_eq!(collapse, z0, "s^0(0) collapses to 0");

        let s3 = e.make_iter(s, 3, z0);
        let s2_s3 = e.make_iter(s, 2, s3); // s^2(s^3(0))
        assert!(e.deep_equal(s2_s3, s5), "s^2(s^3(0)) flattens to s^5(0)");
        assert_eq!(e.node(s2_s3).children().count(), 1, "an S node has one child (the base)");
    }

    /// B3.2 THE soundness gate (the audit's #1 B3 trap): the S `count` is scalar payload, not a child,
    /// so `deep_equal`/`dag_compare` must compare it — else `s^2(0)` and `s^3(0)` (both child `[0]`)
    /// would compare equal.
    #[test]
    fn iter_equality_and_order_use_the_count() {
        let (mut e, _zero, _nznat, _nat, z, s) = iter_ctx();
        let z0 = e.make_const(z);
        let (s2a, s2b, s3) = (e.make_iter(s, 2, z0), e.make_iter(s, 2, z0), e.make_iter(s, 3, z0));
        assert!(e.deep_equal(s2a, s2b), "s^2(0) == s^2(0) (distinct ids, equal count)");
        assert!(!e.deep_equal(s2a, s3), "s^2(0) != s^3(0) — count distinguishes them");
        assert_eq!(e.runtime().dag_compare(s2a, s3), Ordering::Less, "s^2 < s^3 by count");
        assert_eq!(e.runtime().dag_compare(s3, s2a), Ordering::Greater);
        assert_eq!(e.runtime().dag_compare(s2a, s2b), Ordering::Equal);
    }

    /// B3.2 S-theory reduce, ground equation (== reference binary, ITER): `eq s s 0 = 0` rewrites
    /// `s^5(0)` modulo the successor extension — `s^5 -> s^3 -> s^1`, 2 rewrites, result `s 0 : NzNat`.
    #[test]
    fn iter_reduce_ground_equation() {
        let (mut e, _zero, nznat, _nat, z, s) = iter_ctx();
        e.add_equation(Equation {
            lhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]), // s s 0
            rhs: Term::constant(z),
            nr_vars: 0,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1 (2 rewrites)");
        assert_eq!(e.sort_of(r), nznat, "result s 0 : NzNat");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "result is s 0");
    }

    /// B3.2 S-theory reduce, variable equation (== reference binary, ITER-VAR): `eq s s s X = s X`
    /// rewrites `s^5(0) -> s 0` (2 rewrites) and `s^3(0) -> s 0` (1) — the variable absorbs the
    /// successor surplus (the extension's first/whole solution).
    #[test]
    fn iter_reduce_variable_equation() {
        let (mut e, _zero, _nznat, nat, z, s) = iter_ctx();
        let sx = |t| Term::op(s, vec![t]);
        e.add_equation(Equation {
            lhs: sx(sx(sx(Term::var(0, nat)))), // s s s X
            rhs: sx(Term::var(0, nat)),         // s X
            nr_vars: 1,
        });
        let s5 = iter_num(&mut e, z, s, 5);
        let r = e.reduce(s5);
        assert_eq!(e.rewrites(), 2, "s^5 -> s^3 -> s^1");
        let s1 = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r, s1), "s^5 -> s 0");

        e.reset_rewrites();
        let s3 = iter_num(&mut e, z, s, 3);
        let r2 = e.reduce(s3);
        assert_eq!(e.rewrites(), 1, "s^3 -> s 0");
        let s1b = iter_num(&mut e, z, s, 1);
        assert!(e.deep_equal(r2, s1b));
    }

    /// B3.3 built-in seam (== reference binary, `conformance/bool.maude`): `EqualitySymbol` (`_~_`)
    /// reduces to `tt`/`ff` by structural equality (1 rewrite); the lazy `BranchSymbol` (`myif`) selects
    /// a branch and leaves the dead branch **unreduced** (`myif(tt,0,big)` = 0 in 1 rewrite, while
    /// `myif(tt,big,0)` reduces the chosen `big` = `s s 0` for 2). Attached via `set_special`.
    #[test]
    fn builtin_equality_and_branch_over_bool() {
        use crate::symbol::SpecialOp;
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let big = e.add_op("big", vec![], nat);
        e.add_equation(Equation {
            lhs: Term::constant(big), // eq big = s s 0
            rhs: Term::op(s, vec![Term::op(s, vec![Term::constant(z)])]),
            nr_vars: 0,
        });
        let eq = e.add_op("~", vec![nat, nat], truth);
        e.set_special(eq, SpecialOp::Equality { eq: tt, neq: ff });
        let myif = e.add_op("myif", vec![truth, nat, nat], nat);
        e.set_special(myif, SpecialOp::Branch { tests: vec![tt, ff] });

        // _~_ over (reduced) Nat numerals: structural equality → tt/ff, 1 rewrite each.
        let mut eqtest = |a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(&mut e, z, s, a), iter_num(&mut e, z, s, b));
            let q = e.make_free(eq, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(eqtest(2, 2), (tt, 1), "s^2 0 ~ s^2 0 = tt");
        assert_eq!(eqtest(2, 3), (ff, 1), "s^2 0 ~ s^3 0 = ff");
        assert_eq!(eqtest(0, 0), (tt, 1), "0 ~ 0 = tt");

        // myif(tt, 0, big) -> 0, 1 rewrite (dead `big` never reduced).
        e.reset_rewrites();
        let (c, t0, ebig) = (e.make_const(tt), iter_num(&mut e, z, s, 0), e.make_const(big));
        let q = e.make_free(myif, vec![c, t0, ebig]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(tt, 0, big) = 0");
        assert_eq!(e.rewrites(), 1, "selection only — big unreduced");

        // myif(tt, big, 0) -> s s 0, 2 rewrites (selection + big reduces).
        e.reset_rewrites();
        let (c, tbig, e0) = (e.make_const(tt), e.make_const(big), iter_num(&mut e, z, s, 0));
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 2, "selection + big = s s 0");
        let s2 = iter_num(&mut e, z, s, 2);
        assert!(e.deep_equal(r, s2), "myif(tt, big, 0) = s s 0");

        // myif(ff, big, 0) -> 0, 1 rewrite (else branch; big unreduced).
        e.reset_rewrites();
        let (c, tbig, e0) = (e.make_const(ff), e.make_const(big), iter_num(&mut e, z, s, 0));
        let q = e.make_free(myif, vec![c, tbig, e0]);
        let r = e.reduce(q);
        assert_eq!(e.node(r).symbol(), z, "myif(ff, big, 0) = 0");
        assert_eq!(e.rewrites(), 1, "else branch — big unreduced");
    }

    /// B3.4 NAT built-in number ops (== reference binary, `conformance/nat.maude`): `_+_`/`_*_`/`gcd`
    /// (ACU_NumberOp, fold the multiset with multiplicity) and `_quo_`/`_rem_`/`_^_`/`_<_`/`_<=_`
    /// (NumberOp). Each is 1 rewrite; the result sort follows the value (`s^n(0) : NzNat`); a
    /// non-numeric operand survives as ACU residue (`x + 2 + 3 = x + 5`).
    #[test]
    fn builtin_nat_arithmetic_and_comparisons() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let nh = NatHooks { succ: s, zero: z, minus: None }; // NAT: no negatives
        let bh = BoolHooks { true_: tt, false_: ff };
        // ACU ops: NzNat Nat -> NzNat overloaded Nat Nat -> Nat (the prelude shape; F-B-completed).
        let acu_op = |e: &mut Engine, name: &'static str, op: NumOp| -> SymbolId {
            let o = e.add_op_ac(name, vec![nznat, nat], nznat, None);
            e.add_op_decl(o, vec![nat, nat], nat);
            e.set_special(o, SpecialOp::AcuNumberOp { op, nat: nh });
            o
        };
        let plus = acu_op(&mut e, "+", NumOp::Add);
        let times = acu_op(&mut e, "*", NumOp::Mul);
        let gcd = acu_op(&mut e, "gcd", NumOp::Gcd);
        // free arithmetic → Nat, and relational → Truth.
        let num_op = |e: &mut Engine, name: &'static str, op: NumOp, b: Option<BoolHooks>| -> SymbolId {
            let rng = if b.is_some() { truth } else { nat };
            let o = e.add_op(name, vec![nat, nat], rng);
            e.set_special(o, SpecialOp::NumberOp { op, nat: nh, bool_: b });
            o
        };
        let quo = num_op(&mut e, "quo", NumOp::Quo, None);
        let rem = num_op(&mut e, "rem", NumOp::Rem, None);
        let pow = num_op(&mut e, "^", NumOp::Pow, None);
        let lt = num_op(&mut e, "<", NumOp::Lt, Some(bh));
        let le = num_op(&mut e, "<=", NumOp::Le, Some(bh));
        let x = e.add_op("x", vec![], nat);

        // ACU op of two numerals → (decoded value, sort, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, SortId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.sort_of(r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, 3), (5, nznat, 1), "2 + 3 = 5");
        assert_eq!(acu(&mut e, plus, 2, 2), (4, nznat, 1), "2 + 2 = 4 (multiplicity fold)");
        assert_eq!(acu(&mut e, plus, 0, 5), (5, nznat, 1), "0 + 5 = 5");
        assert_eq!(acu(&mut e, times, 3, 4), (12, nznat, 1), "3 * 4 = 12");
        assert_eq!(acu(&mut e, times, 2, 2), (4, nznat, 1), "2 * 2 = 4");
        assert_eq!(acu(&mut e, gcd, 12, 18), (6, nznat, 1), "gcd(12, 18) = 6");

        // Free arithmetic op of two numerals → (decoded value, rewrites).
        let arith = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (u64, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (decode_nat(e, r), e.rewrites())
        };
        assert_eq!(arith(&mut e, quo, 7, 2), (3, 1), "7 quo 2 = 3");
        assert_eq!(arith(&mut e, rem, 7, 2), (1, 1), "7 rem 2 = 1");
        assert_eq!(arith(&mut e, pow, 2, 10), (1024, 1), "2 ^ 10 = 1024");

        // Relational op → Truth constant.
        let cmp = |e: &mut Engine, op: SymbolId, a: u64, b: u64| -> (SymbolId, u64) {
            e.reset_rewrites();
            let (na, nb) = (iter_num(e, z, s, a), iter_num(e, z, s, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (e.node(r).symbol(), e.rewrites())
        };
        assert_eq!(cmp(&mut e, lt, 2, 3), (tt, 1), "2 < 3 = tt");
        assert_eq!(cmp(&mut e, lt, 3, 2), (ff, 1), "3 < 2 = ff");
        assert_eq!(cmp(&mut e, le, 3, 3), (tt, 1), "3 <= 3 = tt");

        // Residue: x + 2 + 3 = x + 5 (the non-numeric x survives), NzNat, 1 rewrite.
        e.reset_rewrites();
        let (xn, n2, n3) = (e.make_const(x), iter_num(&mut e, z, s, 2), iter_num(&mut e, z, s, 3));
        let q = e.make_ac(plus, vec![xn, n2, n3]);
        let r = e.reduce(q);
        assert_eq!(e.rewrites(), 1, "x + 2 + 3 = x + 5 in 1 rewrite");
        assert_eq!(e.sort_of(r), nznat, "x + 5 : NzNat (asymmetric overload, F-B)");
        assert_eq!(e.node(r).symbol(), plus, "result is still a + node");
        let kids: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(kids.len(), 2, "x + 5 has two operands");
        let mut has_x = false;
        let mut has_5 = false;
        for k in kids {
            if e.node(k).symbol() == x {
                has_x = true;
            } else if decode_nat(&e, k) == 5 {
                has_5 = true;
            }
        }
        assert!(has_x && has_5, "x + 5 = {{x, s^5(0)}}");
    }

    /// B3.5 INT signed arithmetic (== reference binary, `conformance/int.maude`): negatives are
    /// `-(s^n(0))` via `MinusSymbol` (a negative numeral is canonical — 0 rewrites; `-(-x)` and `-0`
    /// reduce in 1). The same ACU/Number ops as NAT, lifted to signed via the `minus` hook; `quo`/`rem`
    /// truncate toward zero. The result sort follows the value (`NzInt`/`NzNat`/`Zero`).
    #[test]
    fn builtin_int_signed_arithmetic() {
        use crate::symbol::{BoolHooks, NatHooks, NumOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint); // -_ : NzNat -> NzInt
        e.add_op_decl(minus, vec![int], int); //          -_ : Int -> Int
        let nh = NatHooks { succ: s, zero: z, minus: Some(minus) };
        let bh = BoolHooks { true_: tt, false_: ff };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let plus = e.add_op_ac("+", vec![int, int], int, None);
        e.set_special(plus, SpecialOp::AcuNumberOp { op: NumOp::Add, nat: nh });
        let times = e.add_op_ac("*", vec![int, int], int, None);
        e.set_special(times, SpecialOp::AcuNumberOp { op: NumOp::Mul, nat: nh });
        let sub = e.add_op("-bin", vec![int, int], int);
        e.set_special(sub, SpecialOp::NumberOp { op: NumOp::Sub, nat: nh, bool_: None });
        let quo = e.add_op("quo", vec![int, nzint], int);
        e.set_special(quo, SpecialOp::NumberOp { op: NumOp::Quo, nat: nh, bool_: None });
        let rem = e.add_op("rem", vec![int, nzint], int);
        e.set_special(rem, SpecialOp::NumberOp { op: NumOp::Rem, nat: nh, bool_: None });
        let lt = e.add_op("<", vec![int, int], truth);
        e.set_special(lt, SpecialOp::NumberOp { op: NumOp::Lt, nat: nh, bool_: Some(bh) });

        // Build a signed numeral `v` (`s^v(0)`, or `-(s^|v|(0))`).
        let mk = |e: &mut Engine, v: i64| -> DagId {
            if v >= 0 {
                iter_num(e, z, s, v as u64)
            } else {
                let p = iter_num(e, z, s, (-v) as u64);
                e.make_free(minus, vec![p])
            }
        };
        // Decode a signed numeral.
        let di = |e: &Engine, id: DagId| -> i64 {
            match &e.node(id).term {
                NodeTerm::Free { symbol, args } if *symbol == minus && args.len() == 1 => {
                    -(decode_nat(e, args[0]) as i64)
                }
                _ => decode_nat(e, id) as i64,
            }
        };

        // Negation: `- 3` is canonical (0 rewrites); `- - 3` and `- 0` reduce in 1.
        e.reset_rewrites();
        let m3 = mk(&mut e, -3);
        let r = e.reduce(m3);
        assert_eq!((di(&e, r), e.rewrites()), (-3, 0), "- 3 = -3 (canonical)");
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzInt", "-3 : NzInt");
        e.reset_rewrites();
        let p3 = mk(&mut e, 3);
        let m3a = e.make_free(minus, vec![p3]);
        let mm3 = e.make_free(minus, vec![m3a]);
        let r = e.reduce(mm3);
        assert_eq!((di(&e, r), e.rewrites()), (3, 1), "- - 3 = 3");
        e.reset_rewrites();
        let z0 = e.make_const(z);
        let m0 = e.make_free(minus, vec![z0]);
        let r = e.reduce(m0);
        assert_eq!((di(&e, r), e.rewrites()), (0, 1), "- 0 = 0");

        // Binary ops over an ACU operator (+, *) → (decoded value, rewrites).
        let acu = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_ac(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(acu(&mut e, plus, 2, -5), (-3, 1), "2 + -5 = -3");
        assert_eq!(acu(&mut e, plus, -2, -3), (-5, 1), "-2 + -3 = -5");
        assert_eq!(acu(&mut e, times, 3, -2), (-6, 1), "3 * -2 = -6");
        assert_eq!(acu(&mut e, times, -2, -3), (6, 1), "-2 * -3 = 6");

        // Binary free arithmetic (-, quo, rem) → (decoded value, rewrites).
        let bin = |e: &mut Engine, op: SymbolId, a: i64, b: i64| -> (i64, u64) {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (di(e, r), e.rewrites())
        };
        assert_eq!(bin(&mut e, sub, 2, 5), (-3, 1), "2 - 5 = -3");
        assert_eq!(bin(&mut e, sub, 5, 2), (3, 1), "5 - 2 = 3");
        assert_eq!(bin(&mut e, quo, 7, -2), (-3, 1), "7 quo -2 = -3 (toward zero)");
        assert_eq!(bin(&mut e, rem, -7, 2), (-1, 1), "-7 rem 2 = -1 (dividend's sign)");

        // Comparison → Truth.
        let cmp = |e: &mut Engine, a: i64, b: i64| -> SymbolId {
            e.reset_rewrites();
            let (na, nb) = (mk(e, a), mk(e, b));
            let q = e.make_free(lt, vec![na, nb]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, -2, 3), tt, "-2 < 3 = tt");
        assert_eq!(cmp(&mut e, 3, -2), ff, "3 < -2 = ff");
    }

    /// B3.6 NA theory + STRING + QID (== reference binary, `conformance/string.maude`): strings/qids
    /// are atomic `NodeTerm::Na` constants. `StringOpSymbol` does concat / length / substr /
    /// comparisons; quoted-ids match only themselves via the Na equality arm (through `EqualitySymbol`).
    #[test]
    fn builtin_string_and_qid() {
        use crate::dag::NaValue;
        use crate::symbol::{BoolHooks, NatHooks, SpecialOp, StrOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let str_s = e.add_sort("Str");
        let qid_s = e.add_sort("Qid");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let strsym = e.add_op("<Strings>", vec![], str_s);
        let qidsym = e.add_op("<Qids>", vec![], qid_s);
        let nh = NatHooks { succ: s, zero: z, minus: None };
        let bh = BoolHooks { true_: tt, false_: ff };
        let concat = e.add_op(".", vec![str_s, str_s], str_s);
        e.set_special(concat, SpecialOp::StringOp { op: StrOp::Concat, str_sym: strsym, nat: None, bool_: None, not_found: None });
        let len = e.add_op("len", vec![str_s], nat);
        e.set_special(len, SpecialOp::StringOp { op: StrOp::Length, str_sym: strsym, nat: Some(nh), bool_: None, not_found: None });
        let sub = e.add_op("sub", vec![str_s, nat, nat], str_s);
        e.set_special(sub, SpecialOp::StringOp { op: StrOp::Substr, str_sym: strsym, nat: Some(nh), bool_: None, not_found: None });
        let lt = e.add_op("lt", vec![str_s, str_s], truth);
        e.set_special(lt, SpecialOp::StringOp { op: StrOp::Lt, str_sym: strsym, nat: None, bool_: Some(bh), not_found: None });
        let se = e.add_op("se", vec![str_s, str_s], truth);
        e.set_special(se, SpecialOp::Equality { eq: tt, neq: ff });
        let qe = e.add_op("qe", vec![qid_s, qid_s], truth);
        e.set_special(qe, SpecialOp::Equality { eq: tt, neq: ff });

        let dstr = |e: &Engine, id: DagId| -> String {
            match &e.node(id).term {
                NodeTerm::Na { value: NaValue::Str(v), .. } => v.to_string(),
                _ => panic!("not a string node"),
            }
        };

        // concat
        e.reset_rewrites();
        let (a, b) = (e.make_string(strsym, "ab"), e.make_string(strsym, "cd"));
        let q = e.make_free(concat, vec![a, b]);
        let r = e.reduce(q);
        assert_eq!((dstr(&e, r), e.rewrites()), ("abcd".into(), 1), "\"ab\" . \"cd\" = \"abcd\"");

        // length → Nat (sort follows the value)
        e.reset_rewrites();
        let h = e.make_string(strsym, "hello");
        let q = e.make_free(len, vec![h]);
        let r = e.reduce(q);
        assert_eq!((decode_nat(&e, r), e.rewrites()), (5, 1), "len(\"hello\") = 5");
        assert_eq!(e.sorts().name(e.sort_of(r)), "NzNat");
        let empty = e.make_string(strsym, "");
        let q = e.make_free(len, vec![empty]);
        let r = e.reduce(q);
        assert_eq!(decode_nat(&e, r), 0, "len(\"\") = 0");
        assert_eq!(e.sorts().name(e.sort_of(r)), "Zero");

        // substr(s, start, len)
        e.reset_rewrites();
        let (hh, n1, n3) = (e.make_string(strsym, "hello"), iter_num(&mut e, z, s, 1), iter_num(&mut e, z, s, 3));
        let q = e.make_free(sub, vec![hh, n1, n3]);
        let r = e.reduce(q);
        assert_eq!((dstr(&e, r), e.rewrites()), ("ell".into(), 1), "sub(\"hello\", 1, 3) = \"ell\"");

        // string comparison + NA equality (string + qid)
        let cmp = |e: &mut Engine, op: SymbolId, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (e.make_string(strsym, x), e.make_string(strsym, y));
            let q = e.make_free(op, vec![a, b]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cmp(&mut e, lt, "abc", "abd"), tt, "\"abc\" < \"abd\"");
        assert_eq!(cmp(&mut e, lt, "b", "abc"), ff, "\"b\" < \"abc\" is false");
        assert_eq!(cmp(&mut e, se, "abc", "abc"), tt, "\"abc\" == \"abc\"");
        assert_eq!(cmp(&mut e, se, "abc", "abd"), ff, "\"abc\" == \"abd\" is false");

        // quoted-id NA equality (matches only itself)
        let qcmp = |e: &mut Engine, x: &str, y: &str| -> SymbolId {
            e.reset_rewrites();
            let (a, b) = (e.make_qid(qidsym, x), e.make_qid(qidsym, y));
            let q = e.make_free(qe, vec![a, b]);
            let r = e.reduce(q);
            e.node(r).symbol()
        };
        assert_eq!(qcmp(&mut e, "foo", "foo"), tt, "'foo == 'foo");
        assert_eq!(qcmp(&mut e, "foo", "bar"), ff, "'foo == 'bar is false");
    }

    /// B3.7 FLOAT built-in ops (== reference binary, `conformance/float.maude`): `f64` arithmetic /
    /// negation / abs / sqrt / comparisons via FloatOpSymbol over atomic `NodeTerm::Na` float values
    /// (all free ops). Each built-in is 1 rewrite (`abs(neg(3.0))` is 2).
    #[test]
    fn builtin_float_ops() {
        use crate::dag::NaValue;
        use crate::symbol::{BoolHooks, FltOp, SpecialOp};
        let mut e = Engine::new();
        let truth = e.add_sort("Truth");
        let flt = e.add_sort("Flt");
        e.close_sorts();
        let tt = e.add_op("tt", vec![], truth);
        let ff = e.add_op("ff", vec![], truth);
        let fsym = e.add_op("<Floats>", vec![], flt);
        let bh = BoolHooks { true_: tt, false_: ff };
        let unary = |e: &mut Engine, op: FltOp| -> SymbolId {
            let o = e.add_op("uf", vec![flt], flt);
            e.set_special(o, SpecialOp::FloatOp { op, float_sym: fsym, bool_: None });
            o
        };
        let binary = |e: &mut Engine, op: FltOp| -> SymbolId {
            let o = e.add_op("bf", vec![flt, flt], flt);
            e.set_special(o, SpecialOp::FloatOp { op, float_sym: fsym, bool_: None });
            o
        };
        let (neg, abs, sqrt) = (unary(&mut e, FltOp::Neg), unary(&mut e, FltOp::Abs), unary(&mut e, FltOp::Sqrt));
        let (add, sub, mul, div) = (
            binary(&mut e, FltOp::Add),
            binary(&mut e, FltOp::Sub),
            binary(&mut e, FltOp::Mul),
            binary(&mut e, FltOp::Div),
        );
        let lt = e.add_op("lt", vec![flt, flt], truth);
        e.set_special(lt, SpecialOp::FloatOp { op: FltOp::Lt, float_sym: fsym, bool_: Some(bh) });

        let df = |e: &Engine, id: DagId| -> f64 {
            match &e.node(id).term {
                NodeTerm::Na { value: NaValue::Float(b), .. } => f64::from_bits(*b),
                _ => panic!("not a float node"),
            }
        };
        // Binary arithmetic (results are exact f64 values).
        let bf = |e: &mut Engine, op: SymbolId, a: f64, b: f64| -> (f64, u64) {
            e.reset_rewrites();
            let (na, nb) = (e.make_float(fsym, a), e.make_float(fsym, b));
            let q = e.make_free(op, vec![na, nb]);
            let r = e.reduce(q);
            (df(e, r), e.rewrites())
        };
        assert_eq!(bf(&mut e, add, 1.5, 2.5), (4.0, 1), "1.5 + 2.5 = 4.0");
        assert_eq!(bf(&mut e, sub, 5.0, 1.5), (3.5, 1), "5.0 - 1.5 = 3.5");
        assert_eq!(bf(&mut e, mul, 2.0, 3.0), (6.0, 1), "2.0 * 3.0 = 6.0");
        assert_eq!(bf(&mut e, div, 7.0, 2.0), (3.5, 1), "7.0 / 2.0 = 3.5");
        // Unary functions.
        let uf = |e: &mut Engine, op: SymbolId, a: f64| -> (f64, u64) {
            e.reset_rewrites();
            let na = e.make_float(fsym, a);
            let q = e.make_free(op, vec![na]);
            let r = e.reduce(q);
            (df(e, r), e.rewrites())
        };
        assert_eq!(uf(&mut e, neg, 1.5), (-1.5, 1), "neg(1.5) = -1.5");
        assert_eq!(uf(&mut e, sqrt, 4.0), (2.0, 1), "sqrt(4.0) = 2.0");
        // Nested: abs(neg(3.0)) = 3.0 in 2 rewrites.
        e.reset_rewrites();
        let n3 = e.make_float(fsym, 3.0);
        let negn3 = e.make_free(neg, vec![n3]);
        let absq = e.make_free(abs, vec![negn3]);
        let r = e.reduce(absq);
        assert_eq!((df(&e, r), e.rewrites()), (3.0, 2), "abs(neg(3.0)) = 3.0 in 2 rewrites");
        // Comparison → Truth.
        let cf = |e: &mut Engine, a: f64, b: f64| -> SymbolId {
            e.reset_rewrites();
            let (na, nb) = (e.make_float(fsym, a), e.make_float(fsym, b));
            let q = e.make_free(lt, vec![na, nb]);
            let r = e.reduce(q);
            assert_eq!(e.rewrites(), 1);
            e.node(r).symbol()
        };
        assert_eq!(cf(&mut e, 1.5, 2.5), tt, "1.5 < 2.5 = tt");
        assert_eq!(cf(&mut e, 2.5, 1.5), ff, "2.5 < 1.5 = ff");
    }

    /// B3.8 RAT — the DivisionSymbol kernel op (== reference binary, `conformance/rat.maude`): `_/_`
    /// canonicalises `I / N` to lowest terms (divide by gcd; denominator 1 → the integer). RAT's
    /// arithmetic is equation-defined (a post-parser milestone), so this is the only RAT kernel op;
    /// `0/N` and an already-canonical fraction do not rewrite.
    #[test]
    fn builtin_division_canonicalizes_rationals() {
        use crate::symbol::{NatHooks, SpecialOp};
        let mut e = Engine::new();
        let zero = e.add_sort("Zero");
        let nznat = e.add_sort("NzNat");
        let nat = e.add_sort("Nat");
        let nzint = e.add_sort("NzInt");
        let int = e.add_sort("Int");
        let nzrat = e.add_sort("NzRat");
        let rat = e.add_sort("Rat");
        e.add_subsort(zero, nat);
        e.add_subsort(nznat, nat);
        e.add_subsort(nznat, nzint);
        e.add_subsort(nat, int);
        e.add_subsort(nzint, int);
        e.add_subsort(nzint, nzrat);
        e.add_subsort(int, rat);
        e.add_subsort(nzrat, rat);
        e.close_sorts();
        let z = e.add_op("0", vec![], zero);
        let s = e.add_op_iter("s", vec![nat], nznat);
        let minus = e.add_op("-", vec![nznat], nzint);
        e.add_op_decl(minus, vec![int], int);
        let nh = NatHooks { succ: s, zero: z, minus: Some(minus) };
        e.set_special(minus, SpecialOp::Minus { nat: nh });
        let div = e.add_op("/", vec![nzint, nznat], nzrat);
        e.add_op_decl(div, vec![int, nznat], rat);
        e.set_special(div, SpecialOp::Division { nat: nh });

        // Build I / N (numerator `n` signed via `-`, denominator `d` positive), reduce, render result.
        let frac = |e: &mut Engine, n: i64, d: u64| -> (String, u64) {
            e.reset_rewrites();
            let nn = if n >= 0 {
                iter_num(e, z, s, n as u64)
            } else {
                let p = iter_num(e, z, s, (-n) as u64);
                e.make_free(minus, vec![p])
            };
            let dn = iter_num(e, z, s, d);
            let q = e.make_free(div, vec![nn, dn]);
            let r = e.reduce(q);
            (rat_str(e, minus, div, r), e.rewrites())
        };
        assert_eq!(frac(&mut e, 4, 2), ("2".into(), 1), "4/2 = 2");
        assert_eq!(frac(&mut e, 12, 16), ("3/4".into(), 1), "12/16 = 3/4");
        assert_eq!(frac(&mut e, 6, 4), ("3/2".into(), 1), "6/4 = 3/2");
        assert_eq!(frac(&mut e, -6, 4), ("-3/2".into(), 1), "-6/4 = -3/2");
        assert_eq!(frac(&mut e, 5, 1), ("5".into(), 1), "5/1 = 5");
        assert_eq!(frac(&mut e, 3, 4), ("3/4".into(), 0), "3/4 already canonical (0 rewrites)");
        assert_eq!(frac(&mut e, 0, 5), ("0/5".into(), 0), "0/5 left to the user eq (0 rewrites)");
    }

    #[test]
    fn reduces_peano_addition() {
        // sorts Nat; ops 0, s_, _+_; eqs  N + 0 = N  and  N + s M = s (N + M)
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);

        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        // peano(n): build s^n(0)
        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let two_a = peano(&mut e, zero, s, 2);
        let two_b = peano(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]); // 2 + 2

        let result = e.reduce(sum);
        let four = peano(&mut e, zero, s, 4);
        assert!(e.deep_equal(result, four), "2 + 2 should reduce to s s s s 0");
        assert_eq!(e.rewrites(), 3, "rewrite count matches reference Maude");
    }

    #[test]
    fn reduces_peano_multiplication() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let times = e.add_op("*", vec![nat, nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        // N + 0 = N ; N + s M = s (N + M)
        e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), Term::constant(zero)]), rhs: v(0), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        // N * 0 = 0 ; N * s M = (N * M) + N
        e.add_equation(Equation { lhs: Term::op(times, vec![v(0), Term::constant(zero)]), rhs: Term::constant(zero), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(times, vec![v(0), s_of(v(1))]),
            rhs: Term::op(plus, vec![Term::op(times, vec![v(0), v(1)]), v(0)]),
            nr_vars: 2,
        });

        fn peano(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
            let mut acc = e.make_const(zero);
            for _ in 0..n {
                acc = e.make_free(s, vec![acc]);
            }
            acc
        }

        let three = peano(&mut e, zero, s, 3);
        let four = peano(&mut e, zero, s, 4);
        let prod = e.make_free(times, vec![three, four]); // 3 * 4
        let result = e.reduce(prod);
        let twelve = peano(&mut e, zero, s, 12);
        assert!(e.deep_equal(result, twelve), "3 * 4 should reduce to s^12 0");
        assert_eq!(e.rewrites(), 21, "rewrite count matches reference Maude");
    }

    #[test]
    fn reduced_flag_invalidated_by_new_equation() {
        // Regression for review R2 H2: a node reduced before an equation is added must not stay
        // cached as canonical. Reduce `a` (no equations) → a; add `a = b`; reduce `a` → b.
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);

        let a0 = e.make_const(a);
        let r1 = e.reduce(a0);
        assert_eq!(e.node(r1).symbol(), a, "no equations yet: a is its own normal form");

        e.add_equation(Equation { lhs: Term::constant(a), rhs: Term::constant(b), nr_vars: 0 });
        let r2 = e.reduce(a0); // same id; must re-reduce despite the earlier REDUCED stamp
        assert_eq!(e.node(r2).symbol(), b, "after adding a = b, reducing a yields b");
    }

    #[test]
    fn ill_sorted_argument_blocks_rewrite_and_lands_in_error_sort() {
        // f : Nat -> Nat applied to a Bool (a different kind): the node lands in Nat's error sort,
        // and `eq f(N:Nat) = z` must NOT fire (a Bool can't match a Nat variable). (Review R2 M4
        // / "error-sort propagation is monotone and safe".)
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        let boolean = e.add_sort("Bool"); // separate kind
        e.close_sorts();
        let z = e.add_op("z", vec![], nat);
        let f = e.add_op("f", vec![nat], nat);
        let t = e.add_op("t", vec![], boolean);
        e.add_equation(Equation {
            lhs: Term::op(f, vec![Term::var(0, nat)]),
            rhs: Term::constant(z),
            nr_vars: 1,
        });

        let tb = e.make_const(t);
        let ft = e.make_free(f, vec![tb]); // f(t): Bool arg not <= Nat
        assert!(e.sorts().sort(e.sort_of(ft)).is_error, "ill-sorted f(t) is in the error sort");
        let r = e.reduce(ft);
        assert_eq!(e.node(r).symbol(), f, "f(t) does not rewrite: N:Nat cannot match a Bool");
    }

    /// Build the unary numeral `s^n 0`.
    fn numeral(e: &mut Engine, zero: SymbolId, s: SymbolId, n: u32) -> DagId {
        let mut acc = e.make_const(zero);
        for _ in 0..n {
            acc = e.make_free(s, vec![acc]);
        }
        acc
    }

    /// Decode a canonical Peano numeral `s^k 0` back to `k` (iteratively, so the *test* can't be the
    /// thing that overflows).
    fn decode(e: &Engine, mut id: DagId, zero: SymbolId, s: SymbolId) -> u32 {
        let mut k = 0;
        loop {
            let sym = e.node(id).symbol();
            if sym == zero {
                return k;
            }
            assert_eq!(sym, s, "not a Peano numeral");
            id = e.node(id).children().next().expect("successor has one child");
            k += 1;
        }
    }

    /// Depth 200_000 is ~4x the old recursive reducer's debug stack cliff (~50k); the recursive
    /// `reduce`/`reduce_args` aborted the *process* here (review R2 C1). The iterative work-stack
    /// must reduce it. `s^N + s^N` drives the deepest recursion the old code had (the addition loop
    /// rebuilds `s(plus(..))` and re-descends ~N frames).
    #[test]
    fn iterative_reduce_handles_deep_addition_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });

        const N: u32 = 200_000;
        let a = numeral(&mut e, zero, s, N);
        let b = numeral(&mut e, zero, s, N);
        let sum = e.make_free(plus, vec![a, b]);
        let r = e.reduce(sum);
        assert_eq!(decode(&e, r, zero, s), 2 * N, "s^N + s^N = s^2N");
    }

    /// A deep chain with no applicable equation: the old `reduce` still descended the whole spine
    /// (`reduce_args` → `reduce(child)`) and overflowed. The result must be the *input* id — change
    /// detection preserves shared structure rather than rebuilding an identical chain.
    #[test]
    fn iterative_reduce_walks_deep_spine_without_overflow() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let chain = numeral(&mut e, zero, s, 200_000);
        let r = e.reduce(chain);
        assert_eq!(r, chain, "no equations: a deep chain is its own normal form (shared id kept)");
    }

    /// Conformance lock against the reference C++ Maude binary (`conformance/fib.maude`): the
    /// iterative reducer must reproduce the *exact* redex sequence — `fib(22) = 17711` in `186579`
    /// rewrites.
    #[test]
    fn fib_22_matches_reference_rewrite_count() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let fib = e.add_op("fib", vec![nat], nat);

        let v = |i| Term::var(i, nat);
        let s_of = |t| Term::op(s, vec![t]);
        let zero_t = || Term::constant(zero);
        e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), zero_t()]), rhs: v(0), nr_vars: 1 });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
            rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
            nr_vars: 2,
        });
        e.add_equation(Equation { lhs: Term::op(fib, vec![zero_t()]), rhs: zero_t(), nr_vars: 0 });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(zero_t())]),
            rhs: s_of(zero_t()),
            nr_vars: 0,
        });
        e.add_equation(Equation {
            lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
            rhs: Term::op(plus, vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])]),
            nr_vars: 1,
        });

        let n = numeral(&mut e, zero, s, 22);
        let q = e.make_free(fib, vec![n]);
        let r = e.reduce(q);
        assert_eq!(decode(&e, r, zero, s), 17711, "fib(22) = 17711");
        assert_eq!(e.rewrites(), 186579, "exact rewrite count matches reference Maude");
    }

    /// C7 forwarding, re-baselined: a *shared, still-reducible* redex is reduced — and counted — **once
    /// total**, not once per occurrence. This test pinned the pre-C7 behaviour (2 rewrites: a rewritten
    /// node was never stamped canonical, so a second reference re-reduced it); its own note said to
    /// re-baseline here once forwarding lands. With the `nf` forward the rewritten node IS stamped and
    /// carries its normal form, so the second reference delivers it without re-reducing — Maude's
    /// shared-DAG count. (A rewrite to a subterm: `s 0 + 0 = s 0` forwards `C` to its own argument `s 0`.)
    #[test]
    fn shared_reducible_redex_is_reduced_once() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        // eq N + 0 = N
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });

        // C = s 0 + 0, built once and shared into both children of f (a genuine DAG share).
        let s0 = numeral(&mut e, zero, s, 1);
        let z = e.make_const(zero);
        let c = e.make_free(plus, vec![s0, z]);
        let root = e.make_free(f, vec![c, c]); // f(C, C), C shared
        let r = e.reduce(root);

        // f(s 0, s 0): the shared C fired `N + 0 = N` once; the second reference forwarded to the result.
        assert_eq!(e.node(r).symbol(), f);
        assert_eq!(e.rewrites(), 1, "shared reducible redex reduced once total (C7 forwarding)");
    }

    /// A [`RootGuard`] pins its node across `gc`; dropping it releases the root (D2 amendment).
    #[test]
    fn root_guard_keeps_node_alive_then_releases_on_drop() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let node = e.make_const(a);
        {
            let _g = e.root(node);
            assert_eq!(e.gc(Vec::new()), 0, "a guarded node survives gc with no extra roots");
            assert_eq!(e.live_nodes(), 1);
        } // guard dropped here
        assert_eq!(e.gc(Vec::new()), 1, "after the guard drops, the node is collected");
        assert_eq!(e.live_nodes(), 0);
    }

    /// `RootGuard::set` retargets the root — e.g. to follow a term as a reduction rewrites it.
    #[test]
    fn root_guard_set_retargets() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let na = e.make_const(a);
        let nb = e.make_const(b);
        let g = e.root(na);
        g.set(nb); // now protecting nb instead of na
        assert_eq!(e.gc(Vec::new()), 1, "na is no longer rooted and is collected");
        assert_eq!(e.live_nodes(), 1);
        assert_eq!(e.node(g.get()).symbol(), b, "the guard now protects nb");
    }

    /// Done-when: safe-point GC during *one* reduction keeps memory bounded. The same `fib`
    /// reduction is run with GC off (capacity grows to the full allocation high-water) and with a
    /// short GC interval (capacity stays near the live working set); the result is unchanged. Roots
    /// in flight (the work-stack + child_result) are kept, so the answer is still correct.
    #[test]
    fn safe_point_gc_bounds_memory_within_one_reduction() {
        fn run(interval: Option<u64>) -> (u32, u64, usize) {
            let mut e = Engine::new();
            let nat = e.add_sort("Nat");
            e.close_sorts();
            let zero = e.add_op("0", vec![], nat);
            let s = e.add_op("s", vec![nat], nat);
            let plus = e.add_op("+", vec![nat, nat], nat);
            let fib = e.add_op("fib", vec![nat], nat);
            let v = |i| Term::var(i, nat);
            let s_of = |t| Term::op(s, vec![t]);
            let zero_t = || Term::constant(zero);
            e.add_equation(Equation { lhs: Term::op(plus, vec![v(0), zero_t()]), rhs: v(0), nr_vars: 1 });
            e.add_equation(Equation {
                lhs: Term::op(plus, vec![v(0), s_of(v(1))]),
                rhs: s_of(Term::op(plus, vec![v(0), v(1)])),
                nr_vars: 2,
            });
            e.add_equation(Equation { lhs: Term::op(fib, vec![zero_t()]), rhs: zero_t(), nr_vars: 0 });
            e.add_equation(Equation { lhs: Term::op(fib, vec![s_of(zero_t())]), rhs: s_of(zero_t()), nr_vars: 0 });
            e.add_equation(Equation {
                lhs: Term::op(fib, vec![s_of(s_of(v(0)))]),
                rhs: Term::op(plus, vec![Term::op(fib, vec![s_of(v(0))]), Term::op(fib, vec![v(0)])]),
                nr_vars: 1,
            });
            e.set_gc_interval(interval);
            let n = numeral(&mut e, zero, s, 20);
            let q = e.make_free(fib, vec![n]);
            let r = e.reduce(q);
            (decode(&e, r, zero, s), e.rewrites(), e.node_capacity())
        }

        let (val_off, rw_off, cap_off) = run(None);
        let (val_on, rw_on, cap_on) = run(Some(20_000));
        assert_eq!(val_off, 6765, "fib(20) = 6765");
        assert_eq!(val_on, 6765, "safe-point GC does not change the result");
        assert_eq!(rw_on, rw_off, "safe-point GC does not change the rewrite count");
        assert!(
            cap_on < cap_off,
            "safe-point GC bounds the arena high-water: {cap_on} (on) vs {cap_off} (off)"
        );
    }

    /// Locks the `set_gc_interval` rooting contract (review finding): with safe-point GC enabled, a
    /// result held across a later reduction survives *iff* it is pinned by a [`RootGuard`]. Here the
    /// rooted result of `2 + 2` is still `s^4 0` after a second, allocation-heavy reduction triggers
    /// collection. (Without the guard the second reduction would reclaim it — a debug stale-handle
    /// panic / release silent error — which is the documented footgun, not tested here.)
    #[test]
    fn safe_point_gc_preserves_a_rooted_result_across_reductions() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        e.set_gc_interval(Some(100)); // collect several times during a reduction

        let two_a = numeral(&mut e, zero, s, 2);
        let two_b = numeral(&mut e, zero, s, 2);
        let sum = e.make_free(plus, vec![two_a, two_b]);
        let four = e.reduce(sum); // s^4 0
        let g = e.root(four); // pin it across the next reduction

        // A second, disjoint reduction whose collections (every ~100 allocs) must not reclaim `four`.
        let big_a = numeral(&mut e, zero, s, 600);
        let big_b = numeral(&mut e, zero, s, 600);
        let big_sum = e.make_free(plus, vec![big_a, big_b]);
        let _ = e.reduce(big_sum);

        assert_eq!(decode(&e, g.get(), zero, s), 4, "the rooted result survives intact");
    }

    /// F-2 (engine-global condition-reduce root set): with in-reduction GC on, a re-entrant condition
    /// reduction must NOT sweep the OUTER reduction's live state. Reducing `pair(a, cond(b))` (`a`, `b`
    /// distinct numerals): reducing `cond(b)` fires a conditional equation whose condition reduces
    /// `b + b` on both sides (allocating enough to trigger several collections), during which `pair`'s
    /// already-reduced first argument `a` is live ONLY in the outer reduce frame. Before the fix the
    /// hazard was avoided by disabling GC for the whole condition (unbounded memory); now GC stays on and
    /// `condition_holds` protects the outer frame + bindings + redex, so `a` survives and the result is
    /// `pair(a, b)` intact. (Without the protected root set a nested collection would reclaim `a`, leaving
    /// a dangling/reused id — `decode` would then panic or read the wrong value.)
    #[test]
    fn safe_point_gc_during_condition_preserves_outer_frame() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        let pair = e.add_op("pair", vec![nat, nat], nat); // a free ctor, no equations
        // cond(X) = X  if  X + X = X + X  — the condition reduces X + X on both sides (allocating), so a
        // nested safe-point GC fires *inside* it; the equality always holds, so cond(X) → X.
        let cond = e.add_op("cond", vec![nat], nat);
        let x = Term::var(0, nat);
        e.add_conditional_equation(
            Term::op(cond, vec![x.clone()]),
            x.clone(),
            1,
            vec![ConditionFragment::Equality {
                lhs: Term::op(plus, vec![x.clone(), x.clone()]),
                rhs: Term::op(plus, vec![x.clone(), x.clone()]),
            }],
        );
        e.set_gc_interval(Some(20)); // collect frequently — several times within the condition reduce

        // Distinct values (so `a` and `b` are distinct nodes): `a` lives only in `pair`'s frame while
        // `cond(b)`'s condition reduces.
        let a = numeral(&mut e, zero, s, 100);
        let b = numeral(&mut e, zero, s, 120);
        let cb = e.make_free(cond, vec![b]);
        let subj = e.make_free(pair, vec![a, cb]);
        let r = e.reduce(subj);

        let children: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(children.len(), 2, "pair keeps its two arguments");
        assert_eq!(decode(&e, children[0], zero, s), 100, "outer-frame sibling survived the condition GC");
        assert_eq!(decode(&e, children[1], zero, s), 120, "cond(b) reduced to b");
    }

    /// F-2, matching (`:=`) condition variant: locks the `solve_condition` *matching* arm's rooting of the
    /// reduced subject — and thus the fresh-var bindings, which are its subterms — across the recursive
    /// solve, under in-reduction GC (a distinct path from the equality arm above). `pickm(X) = Y if
    /// Y := X + X` returns `X + X`; reducing `pickm(b)` reduces `b + b` (allocating → GC fires), and
    /// `pair`'s sibling `a` (outer frame), the subject `b + b`, and the matched `Y` must all survive.
    #[test]
    fn safe_point_gc_during_matching_condition() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);
        let s = e.add_op("s", vec![nat], nat);
        let plus = e.add_op("+", vec![nat, nat], nat);
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::constant(zero)]),
            rhs: Term::var(0, nat),
            nr_vars: 1,
        });
        e.add_equation(Equation {
            lhs: Term::op(plus, vec![Term::var(0, nat), Term::op(s, vec![Term::var(1, nat)])]),
            rhs: Term::op(s, vec![Term::op(plus, vec![Term::var(0, nat), Term::var(1, nat)])]),
            nr_vars: 2,
        });
        let pair = e.add_op("pair", vec![nat, nat], nat);
        let pickm = e.add_op("pickm", vec![nat], nat);
        // pickm(X) = Y  if  Y := X + X  — the `:=` reduces `X + X` (allocating) and binds the fresh `Y` to it.
        e.add_conditional_equation(
            Term::op(pickm, vec![Term::var(0, nat)]),
            Term::var(1, nat),
            2,
            vec![ConditionFragment::Matching {
                pattern: Term::var(1, nat),
                subject: Term::op(plus, vec![Term::var(0, nat), Term::var(0, nat)]),
                fresh_vars: vec![1],
            }],
        );
        e.set_gc_interval(Some(20));

        let a = numeral(&mut e, zero, s, 100);
        let b = numeral(&mut e, zero, s, 60);
        let pb = e.make_free(pickm, vec![b]);
        let subj = e.make_free(pair, vec![a, pb]);
        let r = e.reduce(subj);

        let children: Vec<DagId> = e.node(r).children().collect();
        assert_eq!(children.len(), 2, "pair keeps its two arguments");
        assert_eq!(decode(&e, children[0], zero, s), 100, "outer-frame sibling survived the condition GC");
        assert_eq!(decode(&e, children[1], zero, s), 120, "pickm(b) = b + b = 120 (matched subject survived)");
    }

    /// C7 normal-form forwarding (Half 2), in isolation — no construction dedup needed: a *manually*
    /// shared reducible subterm (the **same** `DagId` referenced twice) is reduced **once**. `< g(a),
    /// g(a) >` with `eq g(a) = b`: out of place, the rewritten `g(a)` node is abandoned, so the second
    /// reference would re-reduce it (2 rewrites); the `nf` forward lets the second reference deliver the
    /// already-computed `b` (1 rewrite, matching Maude's shared-DAG count). Result is `< b, b >` either way.
    #[test]
    fn forwarding_reduces_a_shared_redex_once() {
        let mut e = Engine::new();
        let elem = e.add_sort("E");
        let pair_sort = e.add_sort("P");
        e.close_sorts();
        let a = e.add_op("a", vec![], elem);
        let b = e.add_op("b", vec![], elem);
        let g = e.add_op("g", vec![elem], elem);
        let pair = e.add_op("<_,_>", vec![elem, elem], pair_sort);
        e.add_equation(Equation {
            lhs: Term::op(g, vec![Term::constant(a)]),
            rhs: Term::constant(b),
            nr_vars: 0,
        });

        let a0 = e.make_const(a);
        let ga = e.make_free(g, vec![a0]); // ONE g(a) node…
        let subj = e.make_free(pair, vec![ga, ga]); // …referenced twice (a real shared DAG)
        e.reset_rewrites();
        let r = e.reduce(subj);

        assert_eq!(e.rewrites(), 1, "a shared redex reduces once (forwarding), not once per reference");
        let children: Vec<DagId> = e.node(r).children().collect();
        let bsym = |id| e.node(id).symbol() == b;
        assert!(bsym(children[0]) && bsym(children[1]), "both arguments forwarded to b: < b, b >");
    }
}
