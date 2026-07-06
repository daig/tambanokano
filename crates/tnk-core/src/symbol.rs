//! Operator symbols.
//!
//! Phase 0 carried a name and a single sort declaration (`domain -> range`). Stage B1 adds the
//! **equational axioms** an operator is declared with (`assoc`/`comm`/`id:`), which select the
//! operator's *theory* — the term representation and matching algorithm used for it. Per decision
//! **D3** the theory is a closed `enum` (no `Symbol`-is-a-`Theory` inheritance); the axioms are plain
//! data on the symbol and [`Symbol::theory`] classifies them. Ad-hoc overloading (multiple
//! declarations + sort diagram) and the remaining attributes are layered on later by composition.
//!
//! Fields are `pub(crate)`; read access is through getters (review R3 H4).

use crate::id::Id;
use crate::sort::SortId;

pub type SymbolId = Id<Symbol>;

/// The equational axioms an operator is declared with (Maude's `assoc`/`comm`/`id:` attributes).
/// `idem` (and the assoc-only / comm-only theories) are later B1 sub-steps; this slice handles the
/// **ACU** combination (`assoc comm`, optionally with a two-sided identity).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct Axioms {
    pub assoc: bool,
    pub comm: bool,
    /// Idempotence (`f(a, a) = a`) — only meaningful for the commutative, non-associative CUI theory
    /// in this slice (`idem` cannot combine with `assoc`).
    pub idem: bool,
    /// Iteration (`iter`, B3): a unary "stacked successor" operator (`s_`) whose node stores the
    /// iteration count compactly (the **S theory**). Mutually exclusive with assoc/comm/idem.
    pub iter: bool,
}

/// Which equational theory an operator belongs to — selects its `DagNode` representation and its
/// matching automaton (decision **D3**: a closed enum, enum-dispatched). This slice implements
/// [`Free`](Theory::Free), [`Acu`](Theory::Acu), and [`Au`](Theory::Au); `Cui`/`S`/`Na` are later.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Theory {
    /// No structural axioms: `symbol(args...)` matched by direct structural recursion.
    Free,
    /// Associative + commutative (with an optional two-sided identity): a flattened **multiset** of
    /// arguments, matched modulo AC(+U).
    Acu,
    /// Associative (with an optional two-sided identity), **not** commutative: a flattened **ordered
    /// sequence** of arguments, matched modulo A(+U) — e.g. lists, string concatenation.
    Au,
    /// Commutative (with optional identity and/or idempotence), **not** associative: a binary node
    /// with canonically-ordered arguments, matched modulo C(+U+I).
    Cui,
    /// Iteration (`iter`, B3): a unary successor `s_` stored as `s^count(arg)` with a bignum `count`,
    /// matched modulo the stacked-successor extension (`s^k` matches `s^n` for `k <= n`).
    S,
}

/// One operator declaration: argument sorts (`domain`) → `range`, plus whether it is a constructor
/// (`[ctor]`). An operator may carry several declarations (ad-hoc / subsort overloading); the least
/// sort of an application is resolved across all of them (`Signature::compute_sort`). `ctor` is
/// carried now and consumed when the constructor diagram lands (a later B2 sub-step).
#[derive(Debug, Clone)]
pub(crate) struct OpDeclaration {
    pub domain: Vec<SortId>,
    pub range: SortId,
    /// `[ctor]` flag (B2.4). Metadata for functional reduction — a `[ctor]` operator reduces exactly as
    /// a non-`ctor` one (verified against the binary); it marks the operator as a constructor for the
    /// later sufficient-completeness / constructor-diagram analysis.
    pub ctor: bool,
}

#[derive(Debug, Clone)]
pub struct Symbol {
    pub(crate) name: String,
    /// Operator declarations (≥ 1; the first is the original). Overloads share name + arity; sort
    /// resolution walks them **in declaration order**, so order is load-bearing for the
    /// non-preregular least-sort tie-break.
    pub(crate) decls: Vec<OpDeclaration>,
    /// The structural axioms this operator is declared with.
    pub(crate) axioms: Axioms,
    /// The operator's two-sided identity (`id: <term>`), if any. Stored as the **constant** symbol
    /// that is the identity (every conformance target — `0`/`empty`/`e` — is a constant); a general
    /// identity *term* is a later generalization. Canonicalization drops identity arguments and a
    /// matched AC variable may bind this constant (the "collapse to unit" solutions).
    pub(crate) identity: Option<SymbolId>,
    /// Evaluation strategy `strat (…)` (B2.4): the 0-based argument positions to reduce, in order,
    /// before a top rewrite. `None` is the standard strategy (reduce every argument left-to-right); a
    /// custom strategy may leave arguments unreduced (lazy) — e.g. `if_then_else_fi` with `strat (1 0)`.
    pub(crate) strategy: Option<Vec<u32>>,
    /// Frozen arguments (`frozen` / `frozen (…)`, Pillar A): the 0-based argument positions that
    /// `rewrite`/`frewrite`/`search` must **not** rewrite within. `None` = no frozen args; `Some([])` =
    /// all arguments frozen (`[frozen]`); `Some([0,2])` = those positions. Inert for equational `reduce`.
    pub(crate) frozen: Option<Vec<u32>>,
    /// Built-in reduction rule (`special (id-hook …)`, B3), if any — tried before user equations.
    pub(crate) special: Option<SpecialOp>,
    /// Object-system role flags (`config`/`obj`/`msg`/`portal` operator attributes), Pillar 2.5. Inert
    /// for `reduce`/`rewrite`/`frewrite`/`search` — the `config` ACU `__` rewrites as an ordinary ACU
    /// soup. Consumed by the `erewrite` object-message scheduler (Phase 2.5-B) to partition the soup.
    pub(crate) oo: OoFlags,
    /// Classification for the decompose-equality stability analysis (Maude's `SymbolType` basic
    /// types, collapsed to what `.=.` consults). `Standard` is every ordinary user operator.
    pub(crate) class: SymbolClass,
}

/// The `.=.`-relevant slice of Maude's `SymbolType` basic types: a symbol is *equationally stable*
/// (its top cannot change under instantiation, axioms, or equational rewriting — the precondition
/// for `CommutativeDecomposeEqualitySymbol` to decompose or decide `false`) only when it is
/// `Standard`, has no `special`, no identity element, and no equations indexed at it.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum SymbolClass {
    #[default]
    Standard,
    /// A command-subject variable realized as a fresh nullary constant (`build_subject_dag`):
    /// Maude's `VariableSymbol` — never stable, never ground. `rank` is the variable's interned
    /// name-token index (Maude's `Token` code): same-sort variables order by `id() - id()` on name
    /// codes (variableDagNode.cc `compareArguments`), which `dag_compare` mirrors.
    Variable { rank: u32 },
    /// A builtin marker-class symbol whose id-hook attaches no [`SpecialOp`] (`s_`'s `SuccSymbol`,
    /// `<Floats>`/`<Strings>`/`<Qids>`, `true`/`false`, the object constructor): non-`STANDARD` in
    /// Maude's `SymbolType`, hence never equationally stable (verified: NAT's builtin `s X .=. s Y`
    /// stays unreduced in the oracle while a user `[iter ctor]` op decomposes).
    Marker,
}

/// The object-system role of an operator — Maude's `SymbolType` `CONFIG`/`OBJECT`/`MESSAGE`/`PORTAL`
/// bits (`symbolType.hh`), set from the `config`/`obj`/`msg`/`portal` operator attributes
/// (`obj`≡`object`, `msg`≡`message`, `config`≡`configuration`). The roles are independent bits (an op
/// could in principle carry more than one), matching the C++ flag word. The `erewrite` scheduler keys
/// its soup partition on these — **not** on the `Object`/`Msg` sorts (see the plan §2.8 / hazards).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct OoFlags {
    /// `config` — the configuration multiset constructor (`__`), built as a `ConfigSymbol` in C++.
    pub(crate) config: bool,
    /// `obj`/`object` — the object constructor (`<_:_|_>`).
    pub(crate) object: bool,
    /// `msg`/`message` — a message operator.
    pub(crate) message: bool,
    /// `portal` — the external-IO portal (`<>`).
    pub(crate) portal: bool,
}

impl Symbol {
    /// Whether argument position `arg` (0-based) is frozen — a rule may not rewrite within it
    /// (Pillar A). See [`Symbol::frozen`].
    pub(crate) fn is_frozen_arg(&self, arg: usize) -> bool {
        match &self.frozen {
            None => false,
            Some(v) if v.is_empty() => true, // `[frozen]` = every argument
            Some(v) => v.contains(&(arg as u32)),
        }
    }
}

/// A built-in operator's reduction rule (decision **#6** / **D3**): Maude's `special (id-hook …)` seam
/// as a typed enum resolved at module-build time and dispatched by `match` in symbol reduction — not
/// C++'s attached member-function pointers. `term-hook`/`op-hook` references are resolved to
/// [`SymbolId`]s. This slice has the BOOL operators; NAT/INT arithmetic variants are added with those
/// ops. (Until the parser lands the hooks are supplied programmatically via `Engine::set_special`.)
#[derive(Debug, Clone)]
pub enum SpecialOp {
    /// `_==_` / `_=/=_` (Maude's `EqualitySymbol`): reduce both arguments, compare them structurally,
    /// rewrite to `eq` if equal else `neq` (the `equalTerm`/`notEqualTerm` constants, swapped for
    /// `=/=`).
    Equality { eq: SymbolId, neq: SymbolId },
    /// `_.=._` (Maude's `CommutativeDecomposeEqualitySymbol`, INITIAL-EQUALITY-PREDICATE): the
    /// initial-model equality predicate. On symbolic (non-ground) arguments it *decomposes* over
    /// equationally-stable constructors — free/iter/comm/assoc/AC — into conjunctions/disjunctions
    /// of smaller `.=.` problems, decides `false` where the tops provably differ, and otherwise
    /// stays unreduced. `siblings[k]` is this polymorph's instance at kind `k` (tnk expands `poly`
    /// ops eagerly per kind, so the table is total at build time — Maude instantiates lazily).
    DecomposeEquality {
        eq: SymbolId,
        neq: SymbolId,
        conj: Option<SymbolId>,
        disj: Option<SymbolId>,
        siblings: std::rc::Rc<[Option<SymbolId>]>,
    },
    /// `if_then_else_fi` (Maude's `BranchSymbol`): with the condition reduced (the seam installs a lazy
    /// `strat (1 0)`), select the branch whose position matches the condition among `tests` (the
    /// `term-hook` constants, e.g. `[true, false]`), returning it **unreduced** — the dead branch is
    /// never reduced.
    Branch { tests: Vec<SymbolId> },
    /// `_+_` / `_*_` / `gcd` / `lcm` / `min` / `max` / `_xor_` / `_&_` / `_|_` (Maude's
    /// `ACU_NumberOpSymbol`): fold the **numeric** operands of the ACU multiset (with multiplicity),
    /// rebuilding from the result number and any non-numeric residue operands.
    AcuNumberOp { op: NumOp, nat: NatHooks },
    /// `_quo_` / `_rem_` / `_^_` / `_<<_` / `_>>_` / `_<_` / `_<=_` / `_>_` / `_>=_` / `_divides_`
    /// (Maude's `NumberOpSymbol`): a free op over numeric arguments. Relational ops (`bool_` present)
    /// rewrite to a Bool constant; arithmetic ops to a Nat. A non-numeric argument, division by zero, or
    /// a would-be-negative result falls through to user equations (`None`).
    NumberOp { op: NumOp, nat: NatHooks, bool_: Option<BoolHooks> },
    /// `sd` (Maude's `CUI_NumberOpSymbol`): a **commutative** 2-argument op over numeric arguments —
    /// symmetric difference `sd(m, n) = |m − n|`. The two operands come from the CUI node; the result is
    /// a Nat. A non-numeric argument falls through (`None`).
    CuiNumberOp { op: NumOp, nat: NatHooks },
    /// `-_` (Maude's `MinusSymbol`): integer negation. `-(s^n(0))` is the canonical negative (no
    /// rewrite); `-(-x)` reduces to `x` and `-0` to `0`. `nat.minus` is this operator.
    Minus { nat: NatHooks },
    /// `_+_` (concat) / `length` / `substr` / `ascii` / `char` / `find` / `rfind` / `upperCase` /
    /// `lowerCase` / `_<_`/`_<=_`/`_>_`/`_>=_` over strings (Maude's `StringOpSymbol`): operate on
    /// `NodeTerm::Na` string values. `str_sym` builds string/char results; `nat` (length/substr/ascii/
    /// find), `bool_` (comparisons), and `not_found` (the `notFound` constant for find/rfind) are the
    /// result-type hooks.
    StringOp {
        op: StrOp,
        str_sym: SymbolId,
        nat: Option<NatHooks>,
        bool_: Option<BoolHooks>,
        not_found: Option<SymbolId>,
    },
    /// Float arithmetic / functions / comparisons (Maude's `FloatOpSymbol`): operate on `NodeTerm::Na`
    /// float (`f64`) values. `float_sym` builds float results; `bool_` is the comparison result hook.
    FloatOp { op: FltOp, float_sym: SymbolId, bool_: Option<BoolHooks> },
    /// `random : Nat -> Nat` (Maude's `RandomOpSymbol`): the n-th 32-bit output of MT19937 (Mersenne
    /// Twister) seeded with 0 — a deterministic pure function of `n`.
    Random { nat: NatHooks },
    /// `counter : -> [Nat]` (Maude's `CounterSymbol`): a **stateful rule-special** — inert under `reduce`
    /// (left as the kind constant), but each `rewrite`/`frewrite` step that meets a `counter` redex yields
    /// the next natural (0, 1, 2, …), reset per top-level rewriting command. Handled in the rewrite
    /// traversal, not `try_special`.
    Counter { nat: NatHooks },
    /// `string : Qid -> String` / `qid : String ~> Qid` (Maude's `QuotedIdentifierOpSymbol`): convert
    /// between a quoted identifier and its text. `qid_sym`/`str_sym` build the respective NA results.
    QidOp { op: QidOp, qid_sym: SymbolId, str_sym: SymbolId },
    /// The CONVERSION module's cross-type coercions (`float`/`rat`/`string`/`decFloat`, under Maude's
    /// `FloatOpSymbol`/`StringOpSymbol` with conversion codes). Each `op` uses the subset of hooks it
    /// needs: `float_sym` builds floats, `str_sym` strings, `nat` reads/builds numerals, `division` the
    /// rational `_/_`, `dec_float` the `<_,_,_>` triple.
    Conversion {
        op: ConvOp,
        float_sym: Option<SymbolId>,
        str_sym: Option<SymbolId>,
        nat: Option<NatHooks>,
        division: Option<SymbolId>,
        dec_float: Option<SymbolId>,
    },
    /// `_/_` (Maude's `DivisionSymbol`): canonicalise a rational `I / N` to lowest terms — divide by
    /// `gcd(|I|, N)`, reducing to the integer `I/g` when the denominator becomes 1. RAT's arithmetic
    /// (`+`/`*`/…) is **equation-defined** in the prelude (a module-loading milestone, B5), so this is
    /// the only RAT kernel op. `0/N` is left to the user equation `0/Q = 0`.
    Division { nat: NatHooks },
    /// A META-LEVEL **descent function** (Maude's `MetaLevelOpSymbol`): `metaReduce`/`metaApply`/… — a
    /// reflective operator that down-translates its meta-term arguments into an object module, runs an
    /// engine operation in it, and up-translates the result. The meta-representation symbols it needs are
    /// resolved from the op's `op-hook` list into [`MetaHooks`]; `op` selects which descent function.
    /// Symbolic / SMT / strategy descent ([`MetaOp::Deferred`]) is declared but stays at the kind level
    /// (Phase 3.2/3.3).
    Meta { op: MetaOp, hooks: std::rc::Rc<MetaHooks> },
    /// A standard-stream **external-object manager** (Maude's `StreamManagerSymbol`): the 0-ary `Oid`
    /// constant `stdin`/`stdout`/`stderr` (Pillar 2.5-C). In `erewrite`'s EXTERNAL mode, with a `<>`
    /// portal in the soup, a message targeting this constant is handled by the manager — `stdout`/`stderr`
    /// `write(self, me, str)` emits `str` to the stream and replies `wrote(me, self)` **synchronously**;
    /// `stdin` `getLine` is reactor-async (a later sub-step). The hooks are the message symbols the manager
    /// consumes/produces, resolved from the op's `op-hook` list.
    StreamManager {
        stream: StdStream,
        /// `<Strings>` (the `stringSymbol` op-hook) — builds the `gotLine` payload from a read line.
        string_sym: Option<SymbolId>,
        write_msg: Option<SymbolId>,
        wrote_msg: Option<SymbolId>,
        get_line_msg: Option<SymbolId>,
        got_line_msg: Option<SymbolId>,
    },
}

/// Which standard stream a [`SpecialOp::StreamManager`] drives (Maude's `StreamManagerSymbol` data).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StdStream {
    Stdin,
    Stdout,
    Stderr,
}

/// Which META-LEVEL descent function a [`SpecialOp::Meta`] performs (Maude's `MetaLevelOpSymbol` code).
/// The reflection-core functions (Phase 3.1) have their own variants; the symbolic/variant/narrowing,
/// SMT, and strategy descent functions — gated on the BDD (D6) and Z3 (D7) backends and the strategy
/// language (Phase 2 item 4) — collapse to [`MetaOp::Deferred`] (declared, inert).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MetaOp {
    Reduce,
    Normalize,
    Rewrite,
    Frewrite,
    Apply,
    Xapply,
    Match,
    Xmatch,
    Search,
    SearchPath,
    SortLeq,
    SameKind,
    LesserSorts,
    GlbSorts,
    LeastSort,
    CompleteName,
    GetKind,
    GetKinds,
    MaximalSorts,
    MinimalSorts,
    MaximalAritySet,
    Parse,
    PrettyPrint,
    PrintToString,
    WellFormedModule,
    WellFormedTerm,
    WellFormedSubstitution,
    UpModule,
    UpImports,
    UpSorts,
    UpSubsortDecls,
    UpOpDecls,
    UpMbs,
    UpEqs,
    UpRls,
    UpStratDecls,
    UpSds,
    UpView,
    UpTerm,
    DownTerm,
    /// Symbolic / SMT / strategy descent — declared so the tower loads, but inert (kind-level).
    Deferred,
}

/// The meta-representation symbols a [`SpecialOp::Meta`] descent function needs, resolved from its
/// operator's `op-hook`/`term-hook` list at module-build time and keyed by hook purpose
/// (`qidSymbol`, `metaTermSymbol`, `succSymbol`, …). The down/up maps look these up to read and build
/// meta-terms. (Populated in the reflection-core stage; empty while descent is inert.)
#[derive(Debug, Clone, Default)]
pub struct MetaHooks {
    pub ops: std::collections::HashMap<String, SymbolId>,
    pub terms: std::collections::HashMap<String, SymbolId>,
}

/// The float operation a [`SpecialOp::FloatOp`] performs (Maude's `FloatOpSymbol` codes): IEEE `f64`
/// arithmetic, the unary functions (`floor`/`ceiling`/`exp`/`log`/`sqrt`/trig), `rem`/`^`/`min`/`max`,
/// and comparisons. (`float`/`rat` conversions are CONVERSION ops, handled separately.)
#[derive(Debug, Clone, Copy)]
pub enum FltOp {
    // Unary.
    Neg,
    Abs,
    Sqrt,
    Floor,
    Ceiling,
    Exp,
    Log,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    // Binary arithmetic.
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Pow,
    Min,
    Max,
    Atan2,
    // Binary comparison → Bool.
    Lt,
    Le,
    Gt,
    Ge,
}

/// A CONVERSION coercion a [`SpecialOp::Conversion`] performs (distinguished by code + arity at build
/// time, since `float`/`rat`/`string` are overloaded across argument types).
#[derive(Debug, Clone, Copy)]
pub enum ConvOp {
    /// `float : Rat -> Float` — the nearest double to a rational.
    RatToFloat,
    /// `rat : FiniteFloat -> Rat` — the exact rational value of a double.
    FloatToRat,
    /// `string : Rat NzNat -> String` — a rational rendered in a base.
    RatToString,
    /// `rat : String NzNat -> Rat` — a rational parsed from a base.
    StringToRat,
    /// `string : Float -> String` — a float's canonical decimal string.
    FloatToString,
    /// `float : String -> Float` — a float parsed from a string.
    StringToFloat,
    /// `decFloat : Float Nat -> DecFloat` — a float decomposed into `< sign·int, "digits", exp >`.
    DecFloat,
}

/// The quoted-identifier conversion a [`SpecialOp::QidOp`] performs (Maude's `QuotedIdentifierOpSymbol`
/// codes `string`/`qid`).
#[derive(Debug, Clone, Copy)]
pub enum QidOp {
    /// `string : Qid -> String` — the identifier text (without the leading quote).
    String,
    /// `qid : String ~> Qid` — a quoted identifier from text (partial: a single-token identifier).
    Qid,
}

/// The string operation a [`SpecialOp::StringOp`] performs (Maude's `StringOpSymbol` codes): concat /
/// length / substr / ascii / char / find / rfind / case-mapping / comparisons.
#[derive(Debug, Clone, Copy)]
pub enum StrOp {
    Concat,
    Length,
    Substr,
    /// `ascii : Char -> Nat` — the code of a single-character string.
    Ascii,
    /// `char : Nat ~> Char` — the one-character string for a code (partial: a valid scalar value).
    Char,
    /// `find : String String Nat -> FindResult` — first index of the pattern at/after the start.
    Find,
    /// `rfind : String String Nat -> FindResult` — last index of the pattern at/before the start.
    Rfind,
    UpperCase,
    LowerCase,
    /// A character-class predicate `isX : Char -> Bool` (STRING-OPS — C `iscntrl`/`isalpha`/…).
    IsClass(CharClass),
    /// `startsWith` / `endsWith : String String -> Bool`.
    StartsWith,
    EndsWith,
    /// `trimStart` / `trimEnd` / `trim : String -> String` (strip C-whitespace).
    TrimStart,
    TrimEnd,
    Trim,
    Lt,
    Le,
    Gt,
    Ge,
}

/// A C `ctype` character class (STRING-OPS's `isControl`/`isAlphabetic`/… predicates), tested per byte in
/// the C locale (a non-ASCII char is in no class).
#[derive(Debug, Clone, Copy)]
pub enum CharClass {
    Control,
    Printable,
    Space,
    Blank,
    Graphic,
    Punct,
    Alnum,
    Alpha,
    Upper,
    Lower,
    Digit,
    XDigit,
}

/// The `op-hook succSymbol` (an `iter` successor) and its `Zero` constant (the successor's `zeroTerm`),
/// plus the optional `op-hook minusSymbol` (`-_`). The numeral bridge uses these to recognise and build
/// `0` / `s^n(0)` / `-(s^n(0))`. `minus` is `None` for `NAT` (no negatives — a negative result falls
/// through to user equations) and `Some` for `INT`.
#[derive(Debug, Clone, Copy)]
pub struct NatHooks {
    pub succ: SymbolId,
    pub zero: SymbolId,
    pub minus: Option<SymbolId>,
}

/// A relational number op's `term-hook trueTerm`/`falseTerm` result constants.
#[derive(Debug, Clone, Copy)]
pub struct BoolHooks {
    pub true_: SymbolId,
    pub false_: SymbolId,
}

/// The arithmetic / relational operation a numeric built-in performs (Maude packs these as a 2-char
/// `CODE` int in `numberOpSymbol.cc`; a typed enum here — decision #6). The arithmetic ops return a
/// `Nat`, the relational ops a `Bool`.
#[derive(Debug, Clone, Copy)]
pub enum NumOp {
    // ACU (fold the multiset) — `_+_` `_*_` `gcd` `lcm` `min` `max`.
    Add,
    Mul,
    Gcd,
    Lcm,
    Min,
    Max,
    // ACU **bitwise** (fold the multiset, multiplicity-aware) — `_xor_` `_&_` `_|_`. `xor` cancels in
    // pairs (an element folded an even number of times contributes nothing); `&`/`|` are idempotent.
    Xor,
    And,
    Or,
    // CUI (commutative 2-arg) — `sd` (symmetric difference `|m − n|`).
    Sd,
    // free arithmetic → Nat/Int — `_-_` (INT) `_quo_` `_rem_` `_^_` `modExp` `_>>_` `_<<_` `abs` `~`.
    Sub,
    Quo,
    Rem,
    Pow,
    ModExp,
    Shr,
    Shl,
    /// `abs : Int -> Nat` — magnitude. Free unary.
    Abs,
    /// `~_ : Int -> Int` — bitwise complement (`~x = -(x+1)`, two's complement). Free unary.
    BitNot,
    // free relational → Bool — `_<_` `_<=_` `_>_` `_>=_` `_divides_`.
    Lt,
    Le,
    Gt,
    Ge,
    Divides,
}

impl Symbol {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn arity(&self) -> usize {
        self.decls[0].domain.len()
    }

    /// The operator's declarations (≥ 1); least-sort resolution walks them in declaration order.
    pub(crate) fn decls(&self) -> &[OpDeclaration] {
        &self.decls
    }

    /// The operator's equational theory (decision **D3**), classified from its [`Axioms`]:
    /// `assoc & comm` → [`Acu`](Theory::Acu); `assoc` only → [`Au`](Theory::Au); `comm`, `id:`, or
    /// `idem` (any subset, non-assoc) → [`Cui`](Theory::Cui) — Maude's CUI_Theory covers all {C,U,I}
    /// combinations, and an `id:`-only / `idem`-only op must still collapse (§3.2 A3c) — else
    /// [`Free`](Theory::Free). Non-comm CUI ops keep positional argument order everywhere; only the
    /// collapse axioms apply.
    pub(crate) fn theory(&self) -> Theory {
        if self.axioms.iter {
            return Theory::S; // `iter` is mutually exclusive with assoc/comm (checked at registration)
        }
        match (self.axioms.assoc, self.axioms.comm) {
            (true, true) => Theory::Acu,
            (true, false) => Theory::Au,
            (false, true) => Theory::Cui,
            (false, false) => {
                if self.identity.is_some() || self.axioms.idem {
                    Theory::Cui
                } else {
                    Theory::Free
                }
            }
        }
    }

    /// The identity constant symbol, if this operator was declared with `id:`.
    pub(crate) fn identity(&self) -> Option<SymbolId> {
        self.identity
    }

    /// The operator's built-in reduction rule (`special (id-hook …)`), if any (B3).
    pub(crate) fn special(&self) -> Option<&SpecialOp> {
        self.special.as_ref()
    }

    /// Whether every declaration of this operator is a constructor (`[ctor]`). Metadata — it does not
    /// affect reduction; recorded for the later constructor analysis (B2.4).
    pub(crate) fn is_constructor(&self) -> bool {
        self.decls.iter().all(|d| d.ctor)
    }
}
