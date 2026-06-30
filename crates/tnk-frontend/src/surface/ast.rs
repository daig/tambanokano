//! Surface AST: the `PreModule` (signature + raw statement bubbles) the surface parser produces before
//! the per-module mixfix term parse runs (B4.4). Term-carrying parts (op identity, equation lhs/rhs,
//! conditions, command terms) are kept as un-parsed token **bubbles**.

use crate::lex::Token;

/// A parsed functional-module skeleton. `Clone` so the module system (B5) can combine the declarations
/// of an import closure into one flattened `PreModule`.
#[derive(Debug, Clone)]
pub struct PreModule {
    pub name: String,
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
/// on `op _,_ to _;_`). Disambiguated `op f : A -> B to g` is still a follow-up, rejected loudly.
#[derive(Debug, Clone)]
pub enum RenameItem {
    Sort { from: String, to: String },
    Op { from: String, to: String, attrs: Attrs },
}

/// A view definition `view V from T to M is <maps> endv` (Pillar B-ii). A view maps a source theory `T`
/// to a target module (or theory) `M`, supplying the concrete sorts/ops that satisfy `T` — the argument of
/// a parameterized-module instantiation `M{V}` (B-iv). `from`/`to` are module expressions; a **parameterized
/// view** `view V{X :: T} from T' to M{X} …` (Axis-A2) carries [`params`](Self::params) and a non-`Named`
/// `to` target, and is exercised by a nested instantiation `M{V{Arg}}` (Axis-A5).
#[derive(Debug, Clone)]
pub struct ViewDecl {
    pub name: String,
    /// Formal parameters `{X :: T, …}` of a *parameterized* view (Axis-A2). Empty for an ordinary view.
    /// A parameterized view is only used by instantiating it (`V{Arg}`) inside a nested module
    /// instantiation; that instantiation substitutes the args into `to`/`sort_maps`/`op_maps`.
    pub params: Vec<Parameter>,
    pub from: ModuleExpr,
    pub to: ModuleExpr,
    /// `sort A to B .` — map a (theory-declared) sort `A` to a sort `B` of the target. Unmapped theory
    /// sorts default to identity (must exist in the target).
    pub sort_maps: Vec<(String, String)>,
    /// `op … to … .` mappings.
    pub op_maps: Vec<OpMap>,
}

/// One operator mapping in a view: `op f to g .` (to another operator) or `op f to term t .` (to a target
/// term, e.g. `op 0 to term 0.0`). Names/terms are raw token bubbles (the mixfix parse runs against the
/// target module later). Disambiguated source `op f : A -> B to …` is a B-ii follow-up (rejected loudly).
#[derive(Debug, Clone)]
pub enum OpMap {
    Op { from: Vec<Token>, to: Vec<Token> },
    Term { from: Vec<Token>, to: Vec<Token> },
}

/// One operator declaration `op <name> : <domain> -> <range> [<attrs>] .` (or `ops …` expanded to one
/// `OpDecl` per name).
#[derive(Debug, Clone)]
pub struct OpDecl {
    /// The mixfix name as raw tokens (`[_+_]`, `[s_]`, `[<_, ,, _>]`, `[gcd]`).
    pub name: Vec<Token>,
    pub domain: Vec<String>,
    pub range: String,
    /// Whether the declaration used the **partial** arrow `~>` (`op _/_ : Float Float ~> Float`). A
    /// partial op's range is the *kind* (error sort): an application that does not reduce sits at the
    /// kind level (`1.0 / 0.0` is `[Float]`), and the built-in/equational result refines it when defined.
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
    Eq { lhs: Vec<Token>, rhs: Vec<Token>, cond: Option<Vec<Token>>, owise: bool, nonexec: bool },
    Mb { lhs: Vec<Token>, sort: Vec<Token>, cond: Option<Vec<Token>>, nonexec: bool },
    /// `rl [\[label\] :] lhs => rhs .` (or `crl … if cond .`). A rule condition may carry a rewrite
    /// fragment `t => p` (Pillar A-v) in addition to the `ceq`-style fragments.
    Rule { label: Option<String>, lhs: Vec<Token>, rhs: Vec<Token>, cond: Option<Vec<Token>>, nonexec: bool },
}

/// A **strategy declaration** `strat name : <domain> @ Sort .` (Pillar 2.4) — names a strategy with its
/// argument sorts (`domain`, empty for a 0-ary strategy) and the **subject sort** it applies to (`@ Sort`).
/// `strats a b : … @ … .` expands to one [`StratDecl`] per name.
#[derive(Debug, Clone)]
pub struct StratDecl {
    pub name: String,
    pub domain: Vec<String>,
    pub subject: String,
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
/// `try`/`not`/`test`/`or-else` desugar to [`StratExpr::Branch`] in the parser.
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
    Apply { label: String, subst: Vec<(Vec<Token>, Vec<Token>)>, substrats: Vec<StratExpr> },
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
    Branch { test: Box<StratExpr>, success: Box<StratExpr>, failure: Box<StratExpr> },
    /// `match P [s.t. C]` / `xmatch` / `amatch` — a test (no rewrite): succeed iff `P` matches.
    Test { kind: TestKind, pattern: Vec<Token>, cond: Option<Vec<Token>> },
    /// `matchrew P [s.t. C] by x1 using E1, …` — match `P`, run `Eᵢ` on the subterm bound to `xᵢ`, rebuild.
    MatchRew { kind: TestKind, pattern: Vec<Token>, cond: Option<Vec<Token>>, subs: Vec<(Vec<Token>, StratExpr)> },
    /// A named strategy `s` / `s(args)`, resolved against the module's `sd`/`csd` definitions.
    Call { name: String, args: Vec<Vec<Token>> },
}

/// A top-level command (functional fragment): `reduce`/`red`, `match`/`xmatch`, the rewriting commands
/// `rewrite`/`rew` + `continue` (Pillar A), and the strategy commands `srewrite`/`dsrewrite` (Pillar 2.4).
#[derive(Debug)]
pub enum Command {
    /// `reduce [in M :] term .`. The optional `module` is Maude's `in <MODULE> :` qualifier — reduce in
    /// that module instead of the current one (a one-shot override; the current module is unchanged).
    Reduce { module: Option<String>, term: Vec<Token> },
    Match { module: Option<String>, pattern: Vec<Token>, subject: Vec<Token>, xmatch: bool },
    /// `rewrite [bound] term .` — rule-fair rewriting to a normal form (or `bound` rule applications).
    Rewrite { module: Option<String>, bound: Option<u64>, term: Vec<Token> },
    /// `frewrite [bound] term .` — position-fair rewriting (Pillar A-ii).
    Frewrite { module: Option<String>, bound: Option<u64>, term: Vec<Token> },
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
    /// `continue [bound] .` — resume the last `rewrite`/`frewrite`/`search` for more steps/solutions.
    Continue { bound: Option<u64> },
    /// `srewrite [in M :] T using E .` (fair) / `dsrewrite …` (depth-first) — strategy-controlled rewriting
    /// (Pillar 2.4). Enumerates the solutions of applying strategy `E` to `T`.
    Srewrite { module: Option<String>, depth_first: bool, term: Vec<Token>, strategy: StratExpr },
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
