//! Surface AST: the `PreModule` (signature + raw statement bubbles) the surface parser produces before
//! the per-module mixfix term parse runs (B4.4). Term-carrying parts (op identity, equation lhs/rhs,
//! conditions, command terms) are kept as un-parsed token **bubbles**.

use crate::lex::Token;

/// Severity carried by a frontend/build diagnostic. Rendering belongs to the Session layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DiagnosticSeverity {
    Warning,
    Error,
}

/// An owned, source-ordered diagnostic produced while parsing or building a module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    pub module: Option<String>,
    pub line: Option<u32>,
    pub subject: Option<String>,
    pub message: String,
}

impl Diagnostic {
    pub fn warning(
        module: impl Into<String>,
        line: Option<u32>,
        subject: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            severity: DiagnosticSeverity::Warning,
            module: Some(module.into()),
            line,
            subject: Some(subject.into()),
            message: message.into(),
        }
    }
}

/// A parsed functional-module skeleton. `Clone` so the module system (B5) can combine the declarations
/// of an import closure into one flattened `PreModule`.
#[derive(Debug, Clone)]
pub struct PreModule {
    pub name: String,
    /// Line of the module-opening keyword when the declaration came from source text.
    pub source_line: Option<u32>,
    /// Nonfatal source diagnostics retained until the Session renders them.
    pub diagnostics: Vec<Diagnostic>,
    /// Functional (`fmod`/`fth`) or system (`mod`/`th`). A system module/theory may declare rules
    /// (`rl`/`crl`); a functional one may not. This is the *rule-gating* axis only.
    pub kind: ModuleKind,
    /// Whether this is a **theory** (`fth`/`th`) rather than a module (`fmod`/`mod`). Orthogonal to
    /// [`kind`](Self::kind) (Maude's `ModuleType` is a bitfield: functional/system ⊥ theory). A theory is
    /// a *specification* — the source of a view and the bound of a parameter (`X :: T`); its statements
    /// are not executed (theory axioms are `[nonexec]` proof obligations). Built with its signature like a
    /// module, but [`nonexec`](Statement) statements are not added to the engine.
    pub is_theory: bool,
    /// Formal parameters `{X :: T, …}` (Pillar B-iii). A parameter `X :: T` makes a *parameter copy* of
    /// theory `T`: each of `T`'s sorts `s` is imported renamed to `X$s` (a parameter sort), so the body can
    /// refer to `X$Elt` and to parameterized sorts `List{X}`. Empty for an ordinary module. The module's
    /// stored [`name`](Self::name) is the bare base (`LIST`, not `LIST{X}`).
    pub params: Vec<Parameter>,
    /// Imported modules (`protecting`/`extending`/`including <module-expr> .`), in declaration order.
    pub imports: Vec<Import>,
    pub sorts: Vec<String>,
    /// Each subsort chain `A B < C < D` as ordered groups (every group is below the next).
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
    /// `true` for a **strategy module/theory** (`smod`/`ssth`) — a system module that additionally permits
    /// strategy declarations/definitions ([`strat_decls`](Self::strat_decls)/[`strat_defs`](Self::strat_defs)).
    /// Orthogonal to [`kind`](Self::kind) (a strategy module is a system module). Plain `mod`/`fmod` = `false`.
    pub is_strategy: bool,
    /// `true` for an **object-oriented module** (`omod`/`oth`, Pillar 2.5-E). An object module is a system
    /// module (rules allowed) that additionally permits `class`/`subclass`/`msg` declarations, which the
    /// parser **desugars** into ordinary sorts/subsorts/ops (so [`ops`](Self::ops) etc. carry the lowered
    /// form and the rest of the pipeline is unchanged). It auto-imports `CONFIGURATION`. The flag is
    /// carried through flattening so `load_statements` runs the **object-pattern completion** transform
    /// (`ooTransform.cc`) — splicing a fresh `AttributeSet` variable into each object pattern and turning a
    /// class *constant* into a fresh class-sorted variable (subclass polymorphism) — only for object modules.
    pub is_object: bool,
    /// `strat`/`strats` declarations (Pillar 2.4) — empty for a non-strategy module.
    pub strat_decls: Vec<StratDecl>,
    /// `sd`/`csd` strategy definitions (Pillar 2.4) — empty for a non-strategy module.
    pub strat_defs: Vec<StratDef>,
}

/// One formal parameter `X :: T` of a parameterized module/view: the parameter name and the theory it is
/// bound by. (Pillar B-iii.)
#[derive(Debug, Clone)]
pub struct Parameter {
    pub name: String,
    pub theory: String,
}

/// Whether a module/theory is functional (`fmod`/`fth` — equations + memberships only) or a system one
/// (`mod`/`th` — may additionally declare rules). The kind gates rule statements (`rl`/`crl`). Whether it
/// is a *theory* is the orthogonal [`PreModule::is_theory`] flag.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleKind {
    Functional,
    System,
}

/// An import declaration: a mode and the module expression it imports. The mode does **not** affect
/// flattening (which declarations are imported) — it is a semantic-check annotation (no-junk /
/// no-confusion), stored for later. So B5 flattens all three modes identically.
#[derive(Debug, Clone)]
pub struct Import {
    pub mode: ImportMode,
    pub expr: ModuleExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportMode {
    Protecting,
    Extending,
    Including,
}

/// A module expression: a named module, a summation `A + B` (the union), a renaming `M * (sort A to B, op f
/// to g)`, or a parameterized **instantiation** `M{V1, …}` (Pillar B-iv) supplying a view per parameter.
#[derive(Debug, Clone)]
pub enum ModuleExpr {
    Named(String),
    Sum(Box<ModuleExpr>, Box<ModuleExpr>),
    Rename(Box<ModuleExpr>, Vec<RenameItem>),
    /// `M{arg, …}` — instantiate the parameterized module `M` with one argument per parameter. Each
    /// argument is itself a module expression (Pillar B Axis-A2/A5): a view name (`Nat`), a nested
    /// instantiation of a parameterized view (`BoxV{ToColor}`, `List{Nat}`), or a bare enclosing-parameter
    /// name (`X`) which `flatten` classifies contextually (a view vs. an enclosing parameter).
    Instantiation(Box<ModuleExpr>, Vec<ModuleExpr>),
}

/// One mapping inside a renaming `* (…)`. Op renaming is by canonical mixfix name (`_,_ to _;_`);
/// the optional `[ … ]` carries attribute *overrides* for the target op (the prelude uses `[prec 43]`
/// on `op _,_ to _;_`). An **arity-disambiguated** op rename `op f : A B -> C to g` carries
/// [`dom_range`](RenameItem::Op::dom_range) — the source domain/range that selects *one* overload of a
/// name shared by several (only that overload is renamed). A `label l to m` renames a statement label.
#[derive(Debug, Clone)]
pub enum RenameItem {
    Sort {
        from: String,
        to: String,
    },
    Op {
        from: String,
        to: String,
        /// `Some((domain, range))` for a disambiguated rename `op f : A B -> C to g` — selects the single
        /// overload of `from` whose signature matches; `None` renames every overload of the name.
        dom_range: Option<(Vec<String>, String)>,
        attrs: Attrs,
    },
    /// `label l to m` — rename a statement label (rule/eq/mb label) `l` to `m`.
    Label {
        from: String,
        to: String,
    },
}

/// A view definition `view V from T to M is <maps> endv` (Pillar B-ii). A view maps a source theory `T`
/// to a target module (or theory) `M`, supplying the concrete sorts/ops that satisfy `T` — the argument of
/// a parameterized-module instantiation `M{V}` (B-iv). `from`/`to` are module expressions; a **parameterized
/// view** `view V{X :: T} from T' to M{X} …` (Axis-A2) carries [`params`](Self::params) and a non-`Named`
/// `to` target, and is exercised by a nested instantiation `M{V{Arg}}` (Axis-A5).
#[derive(Debug, Clone)]
pub struct ViewDecl {
    pub name: String,
    /// Line of the `view` keyword when the declaration came from source text.
    pub source_line: Option<u32>,
    /// Formal parameters `{X :: T, …}` of a *parameterized* view (Axis-A2). Empty for an ordinary view.
    /// A parameterized view is only used by instantiating it (`V{Arg}`) inside a nested module
    /// instantiation; that instantiation substitutes the args into `to`/`sort_maps`/`op_maps`.
    pub params: Vec<Parameter>,
    pub from: ModuleExpr,
    pub to: ModuleExpr,
    /// Variables declared in the view body. They scope operator-to-term mappings but are not part of the
    /// reflected `View` value.
    pub vars: Vec<VarDecl>,
    /// `sort A to B .` — map a (theory-declared) sort `A` to a sort `B` of the target. Unmapped theory
    /// sorts default to identity (must exist in the target).
    pub sort_maps: Vec<(String, String)>,
    /// `op … to … .` mappings.
    pub op_maps: Vec<OpMap>,
}

/// One operator mapping in a view: `op f to g .` (to another operator) or `op f to term t .` (to a target
/// term, e.g. `op 0 to term 0.0`). A disambiguated source `op f : A -> B to …` carries its domain/range
/// profile so one overload can be mapped without affecting another.
#[derive(Debug, Clone)]
pub enum OpMap {
    Op {
        from: Vec<Token>,
        to: Vec<Token>,
        dom_range: Option<(Vec<String>, String)>,
    },
    Term {
        from: Vec<Token>,
        to: Vec<Token>,
        dom_range: Option<(Vec<String>, String)>,
    },
}

/// One operator declaration `op <name> : <domain> -> <range> [<attrs>] .` (or `ops …` expanded to one
/// `OpDecl` per name).
#[derive(Debug, Clone)]
pub struct OpDecl {
    /// The mixfix name as raw tokens (`[_+_]`, `[s_]`, `[<_, ,, _>]`, `[gcd]`).
    pub name: Vec<Token>,
    pub domain: Vec<String>,
    pub range: String,
    /// Whether the declaration used the **partial** arrow `~>` (`op _/_ : Float Float ~> Float`).
    /// Maude lifts every domain and range sort of a partial declaration to its kind (error sort), so
    /// kind-level arguments are accepted and an unreduced application remains at the result kind.
    pub partial: bool,
    pub attrs: Attrs,
}

#[derive(Debug, Clone)]
pub struct VarDecl {
    pub names: Vec<String>,
    pub sort: String,
}

/// Operator attributes (`[assoc comm id: … ctor iter prec gather strat special ditto]`).
#[derive(Debug, Default, Clone)]
pub struct Attrs {
    pub assoc: bool,
    pub comm: bool,
    pub idem: bool,
    pub iter: bool,
    pub ctor: bool,
    /// `id: <term>` identity element (a token bubble).
    pub id: Option<Vec<Token>>,
    pub prec: Option<u32>,
    pub gather: Option<Vec<GatherElem>>,
    /// `strat (…)` — the raw 1-based positions (ending in `0`).
    pub strat: Option<Vec<u32>>,
    /// `frozen` / `frozen (1 2)` — `None` = not frozen; `Some([])` = all arguments frozen (`[frozen]`);
    /// `Some([1,3])` = those 1-based argument positions frozen. A frozen argument is never rewritten by
    /// `rewrite`/`frewrite`/`search` (Pillar A).
    pub frozen: Option<Vec<u32>>,
    pub special: Option<SpecialSpec>,
    pub ditto: bool,
    /// `memo` — retained for an explicit unsupported-feature warning; it has no kernel semantics.
    pub memo: bool,
    /// `poly (<positions>)` — the polymorphic argument/range positions (Maude's `Polymorph`),
    /// numbered with arguments `1..n` and the range as `0`. A position listed here is `Universal`:
    /// `build_sig` expands the op into one concrete declaration per kind, substituting that kind's
    /// error (top) sort at each listed position. `None` = an ordinary, monomorphic op.
    pub poly: Option<Vec<u32>>,
    /// `format (<word> …)` — one format directive word per **gap** of the operator's mixfix form (gaps =
    /// tokens + 1: before each token/hole, plus a trailing one). Each word is a directive string (`d`
    /// default, `s` space, `t` tab, `n` newline, `i` indent, `+`/`-` indent level — e.g. `n++i`, `ni`).
    /// The pretty-printer uses it for `_<-_`/`{_,_,_}`/`rl_=>_[_].` layout; `None` = Maude's default spacing.
    pub format: Option<Vec<String>>,
    /// `config` / `configuration` — the configuration-multiset constructor (`__`), Pillar 2.5. Recorded
    /// onto the kernel symbol; the `erewrite` object-message scheduler keys its soup partition on it.
    pub config: bool,
    /// `obj` / `object` — the object constructor (`<_:_|_>`).
    pub object: bool,
    /// `msg` / `message` — a message operator.
    pub message: bool,
    /// `portal` — the external-IO portal (`<>`).
    pub portal: bool,
    /// `pconst` — a **parameter constant** of a theory (`op c : -> Elt [pconst]`). In a parameterized
    /// module `P{X :: T}` such a constant is referred to as `X$c` (the parameter prefix, like a parameter
    /// sort `X$s`); instantiating `P{V}` maps `X$c` through `V`'s op map for `c`.
    pub pconst: bool,
    /// Which side(s) the `id:` collapses: `left id:` / `right id:` collapse only that side (Maude's
    /// one-sided identity), a plain `id:` is two-sided (fable-audit.md §3.4). Meaningful only when
    /// [`id`](Self::id) is `Some`.
    pub id_side: IdSide,
}

/// The side(s) on which an operator's `id:` identity element collapses at construction/matching. Maude's
/// `assoc [left|right] id:` — a one-sided identity only absorbs an identity argument on its declared side.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum IdSide {
    /// A plain `id:` — collapses on either side (Maude's two-sided identity).
    #[default]
    Both,
    /// `left id:` — only a leading identity argument collapses.
    Left,
    /// `right id:` — only a trailing identity argument collapses.
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GatherElem {
    /// `E` — argument precedence bound = the operator's prec.
    Strong,
    /// `e` — bound = prec − 1.
    Weak,
    /// `&` — no bound (`ANY`).
    Any,
}

/// A `special (id-hook … op-hook … term-hook …)` directive: hook names + their argument bubbles, resolved
/// to a `tnk-core::SpecialOp` by `build_sig` (B4.2).
#[derive(Debug, Default, Clone)]
pub struct SpecialSpec {
    /// `(class_name, data_tokens)` — e.g. `("ACU_NumberOpSymbol", ["+"])`, `("BranchSymbol", [])`.
    pub id_hook: Option<(String, Vec<String>)>,
    /// `op-hook <purpose> (<op-signature>)` — e.g. `("succSymbol", ["s_", ":", "Nat", "~>", "NzNat"])`.
    pub op_hooks: Vec<(String, Vec<Token>)>,
    /// `term-hook <purpose> (<term>)` — e.g. `("zeroTerm", ["0"])`, `("1", ["true"])`.
    pub term_hooks: Vec<(String, Vec<Token>)>,
}

/// A statement — `eq`/`ceq`/`owise`, `mb`/`cmb`, `rl`/`crl`. Term parts are raw bubbles (parsed in B4.4).
/// `nonexec` ([`nonexec`] statement attribute) marks an axiom that is *not* applied during
/// reduction/rewriting — a proof obligation (theory axioms are all `[nonexec]`, but a module statement may
/// be too). Such statements parse and carry through flattening, but are skipped when loading the engine.
#[derive(Debug, Clone)]
pub enum Statement {
    Eq {
        lhs: Vec<Token>,
        rhs: Vec<Token>,
        cond: Option<Vec<Token>>,
        owise: bool,
        variant: bool,
        nonexec: bool,
        label: Option<String>,
    },
    Mb {
        lhs: Vec<Token>,
        sort: Vec<Token>,
        cond: Option<Vec<Token>>,
        nonexec: bool,
        label: Option<String>,
    },
    /// `rl [\[label\] :] lhs => rhs .` (or `crl … if cond .`). A rule condition may carry a rewrite
    /// fragment `t => p` (Pillar A-v) in addition to the `ceq`-style fragments.
    Rule {
        label: Option<String>,
        lhs: Vec<Token>,
        rhs: Vec<Token>,
        cond: Option<Vec<Token>>,
        nonexec: bool,
        /// A rule selected by variant-based narrowing. Independent of `nonexec`: nonexec narrowing
        /// rules participate in symbolic narrowing but never ordinary rewriting.
        narrowing: bool,
    },
}

/// A **strategy declaration** `strat name : <domain> @ Sort .` (Pillar 2.4) — names a strategy with its
/// argument sorts (`domain`, empty for a 0-ary strategy) and the **subject sort** it applies to (`@ Sort`).
/// `strats a b : … @ … .` expands to one [`StratDecl`] per name.
#[derive(Debug, Clone)]
pub struct StratDecl {
    pub name: String,
    pub domain: Vec<String>,
    pub subject: String,
    /// Stable donation identity assigned by the module flattener. Declarations copied from the same
    /// source module share an origin; independently imported declarations do not.
    pub origin: Option<String>,
    /// Position in the source module's strategy-declaration list; paired with `origin` for diamond dedup.
    pub source_index: Option<usize>,
    /// Source module whose grammar owns this declaration. Cleared by source-transforming module
    /// expressions (renaming/instantiation), whose tokens are rewritten for the destination grammar.
    pub home: Option<String>,
}

/// A **strategy definition** `sd name(params) := body .` / `csd … := body if cond .`. The call-pattern
/// arguments (`params`) and any condition are raw token bubbles (parsed against the module grammar at build
/// time, like equation bubbles); the `body` strategy structure is parsed now.
#[derive(Debug, Clone)]
pub struct StratDef {
    pub name: String,
    pub params: Vec<Vec<Token>>,
    pub body: StratExpr,
    pub cond: Option<Vec<Token>>,
    /// Stable donation identity assigned by the module flattener (parallel to [`StratDecl::origin`]).
    pub origin: Option<String>,
    /// Position in the source module's strategy-definition list; paired with `origin` for diamond dedup.
    pub source_index: Option<usize>,
    /// Source module whose grammar owns the raw parameter/body term bubbles.
    pub home: Option<String>,
}

/// A test/matchrew matching mode: `match` (top), `xmatch` (with extension), `amatch` (anywhere).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TestKind {
    Match,
    XMatch,
    AMatch,
}

/// A **strategy expression** (the combinator tree, Table 10.1). Term-carrying parts (a rule label's initial
/// substitution / its rewrite-condition substrategies, a test/matchrew pattern + condition, a call's
/// arguments) are raw token bubbles, parsed against the module grammar at execution time. The derived forms
/// `try`/`not`/`test`/`or-else` keep their surface spelling ([`StratExpr::Sugar`]) for the command echo
/// and desugar to [`StratExpr::Branch`] at resolution (fable-audit.md §3.9.8 ii).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StratSugar {
    Try,
    NotS,
    TestS,
    OrElse,
}

#[derive(Debug, Clone)]
pub enum StratExpr {
    /// `idle` — pass the subject through unchanged (one solution).
    Idle,
    /// `fail` — no solution.
    Fail,
    /// `all` — apply any rule once, anywhere (every one-step rewrite).
    All,
    /// `label[σ]{E,…}` — apply the rule(s) labelled `label`; `subst` is the optional initial substitution
    /// (`x <- t` bubbles), `substrats` the substrategies for the rule's rewrite conditions.
    Apply {
        label: String,
        subst: Vec<(Vec<Token>, Vec<Token>)>,
        substrats: Vec<StratExpr>,
    },
    /// `top(E)` — apply `E` only at the top of the subject.
    Top(Box<StratExpr>),
    /// `one(E)` — at most the first solution of `E`.
    One(Box<StratExpr>),
    /// `E ; F` — run `F` on each solution of `E`.
    Seq(Box<StratExpr>, Box<StratExpr>),
    /// `E | F` — the union of the solutions of `E` and `F`.
    Union(Box<StratExpr>, Box<StratExpr>),
    /// `E *` — zero-or-more iterations (`idle | (E ; E*)`).
    Star(Box<StratExpr>),
    /// `E +` — one-or-more iterations (`E ; E*`).
    Plus(Box<StratExpr>),
    /// `E !` — normalization: iterate `E` to a fixpoint (`E ? (E !) : idle`).
    Normalize(Box<StratExpr>),
    /// `test ? success : failure` — if `test` has ≥1 solution, run `success` on each; else `failure` on the
    /// original subject. The primitive behind `try`/`not`/`test`/`or-else`.
    Branch {
        test: Box<StratExpr>,
        success: Box<StratExpr>,
        failure: Box<StratExpr>,
    },
    /// `match P [s.t. C]` / `xmatch` / `amatch` — a test (no rewrite): succeed iff `P` matches.
    Test {
        kind: TestKind,
        pattern: Vec<Token>,
        cond: Option<Vec<Token>>,
    },
    /// `matchrew P [s.t. C] by x1 using E1, …` — match `P`, run `Eᵢ` on the subterm bound to `xᵢ`, rebuild.
    MatchRew {
        kind: TestKind,
        pattern: Vec<Token>,
        cond: Option<Vec<Token>>,
        subs: Vec<(Vec<Token>, StratExpr)>,
    },
    /// A derived branch form kept in its SURFACE spelling for the command echo — `try(α)`, `not(α)`,
    /// `test(α)`, `or-else(α, β)` — resolution desugars to the `? :` branch (fable-audit.md §3.9.8 ii:
    /// the round-trip must preserve the surface form).
    Sugar {
        kind: StratSugar,
        args: Vec<StratExpr>,
    },
    /// A named strategy `s` / `s(args)`, resolved against the module's `sd`/`csd` definitions.
    Call { name: String, args: Vec<Vec<Token>> },
}

/// A top-level command (functional fragment): `reduce`/`red`, object-level SMT `check`/`smt-search`,
/// `match`/`xmatch`, the rewriting commands `rewrite`/`rew` + `continue` (Pillar A), and the strategy
/// commands `srewrite`/`dsrewrite` (Pillar 2.4).
#[derive(Debug)]
pub enum Command {
    /// `reduce [in M :] term .`. The optional `module` is Maude's `in <MODULE> :` qualifier — reduce in
    /// that module instead of the current one (a one-shot override; the current module is unchanged).
    Reduce {
        module: Option<String>,
        term: Vec<Token>,
    },
    /// `check [in M :] formula .` — object-level SMT query over the given formula.
    Check {
        module: Option<String>,
        term: Vec<Token>,
    },
    Match {
        module: Option<String>,
        pattern: Vec<Token>,
        subject: Vec<Token>,
        xmatch: bool,
    },
    /// `rewrite [bound] term .` — rule-fair rewriting to a normal form (or `bound` rule applications).
    Rewrite {
        module: Option<String>,
        bound: Option<u64>,
        term: Vec<Token>,
    },
    /// `frewrite [bound [, gas]] term .` — position-fair rewriting (Pillar A-ii). `gas` (default 1) is the
    /// number of rule applications per position per pass (fable-audit.md §3.4).
    Frewrite {
        module: Option<String>,
        bound: Option<u64>,
        gas: Option<u64>,
        term: Vec<Token>,
    },
    /// `erewrite [bound [, gas]] term .` — object-message-fair rewriting of a configuration (Pillar 2.5).
    /// `bound` caps **deliveries** (config-level rule rewrites); `gas` (default 1) is the per-position gas
    /// for the non-config fallback.
    ERewrite {
        module: Option<String>,
        bound: Option<u64>,
        gas: Option<u64>,
        term: Vec<Token>,
    },
    /// `search [n,m] subject =>arrow pattern [such that cond] .` (Pillar A-iv): reachability search.
    /// `max_solutions` = `[n]`, `max_depth` = the `[n,m]` second bound.
    Search {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        pattern: Vec<Token>,
        such_that: Option<Vec<Token>>,
    },
    /// `smt-search [n,m] [in M :] subject =>arrow pattern [such that cond] .`: object-level SMT search
    /// syntax. It preserves the same surface contract as `search` while remaining a distinct command
    /// variant for later SMT-specific execution; `=>1`/`=>+`/`=>*`/`=>!` are accepted here and runtime
    /// decides which arrows are supported.
    /// `max_solutions` = `[n]`, `max_depth` = the `[n,m]` second bound.
    SmtSearch {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        pattern: Vec<Token>,
        such_that: Option<Vec<Token>>,
    },
    /// `[irredundant] unify [[bound]] [in M :] T1 =? T2 [/\ …] .` (Pillar S1): order-sorted
    /// unification. `bound` = `[n]` (max unifiers before continuation); `irredundant` selects the
    /// minimal-complete-set filter. `body` is the raw `=?`/`/\`-separated bubble, split by the
    /// command builder.
    Unify {
        module: Option<String>,
        bound: Option<u64>,
        irredundant: bool,
        body: Vec<Token>,
    },
    /// Folding variant generation, optionally computing only the final irredundant survivor set.
    GetVariants {
        module: Option<String>,
        bound: Option<u64>,
        irredundant: bool,
        term: Vec<Token>,
        /// Raw comma-separated terms from `such that … irreducible`.
        blockers: Vec<Token>,
    },
    /// Plain or filtered variant unification. `body` contains one or more `/\`-joined `=?` pairs.
    VariantUnify {
        module: Option<String>,
        bound: Option<u64>,
        filtered: bool,
        body: Vec<Token>,
        blockers: Vec<Token>,
    },
    /// Variant matching; variables in `subject` are treated as constants.
    VariantMatch {
        module: Option<String>,
        bound: Option<u64>,
        pattern: Vec<Token>,
        subject: Vec<Token>,
        blockers: Vec<Token>,
    },
    /// Variant-based narrowing (`vu-narrow` / `fvu-narrow`) with its two option blocks.
    Narrow {
        module: Option<String>,
        max_solutions: Option<u64>,
        max_depth: Option<u64>,
        subject: Vec<Token>,
        arrow: SearchArrow,
        goal: Vec<Token>,
        condition: Option<Vec<Token>>,
        fold: bool,
        vfold: bool,
        path: bool,
        filter: bool,
        delay: bool,
        fvu: bool,
    },
    ShowNarrowing {
        display: NarrowDisplay,
        state: Option<u64>,
    },
    /// `continue [bound] .` — resume the last `rewrite`/`frewrite`/`search` for more steps/solutions.
    Continue { bound: Option<u64> },
    /// `srewrite [in M :] T using E .` (fair) / `dsrewrite …` (depth-first) — strategy-controlled rewriting
    /// (Pillar 2.4). Enumerates the solutions of applying strategy `E` to `T`.
    Srewrite {
        module: Option<String>,
        depth_first: bool,
        term: Vec<Token>,
        strategy: StratExpr,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum NarrowDisplay {
    MostGeneral,
    Frontier,
    Path,
    PathStates,
}

/// The reachability arrow of a `search` command (`=>1` / `=>+` / `=>*` / `=>!`).
#[derive(Debug, Clone, Copy)]
pub enum SearchArrow {
    One,
    Plus,
    Star,
    Bang,
}

/// One top-level item: a module definition, a view definition, or a command. The unit the REPL consumes
/// one at a time (a command here is *untagged* — the REPL binds it to its persistent current module).
#[derive(Debug)]
pub enum TopItem {
    Module(PreModule),
    View(ViewDecl),
    Command(Command),
}

/// The result of surface-parsing a source file: the modules, the view definitions, and the top-level
/// commands, each tagged with the index (into `modules`) of the module it runs against — the most recently
/// entered one, as in Maude.
#[derive(Debug, Default)]
pub struct Source {
    pub modules: Vec<PreModule>,
    pub views: Vec<ViewDecl>,
    pub commands: Vec<(usize, Command)>,
}
