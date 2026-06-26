//! The full Maude `trace` renderer: a [`TraceEvent`] stream → Maude's textual trace, gated by
//! [`TraceFlags`]. The kernel records the structured stream (off by default, zero-cost); this layer
//! renders it after `reduce` returns, reading the frontend's per-statement source metadata
//! (`BuiltModule::{eq_traces,mb_traces}`) to print equation/membership bodies and condition fragments.
//!
//! Faithfulness is verified byte-for-byte (color off) against the reference binary — see the
//! `conformance/trace-*.maude` fixtures and the REPL tests. The flag → section mapping mirrors Maude's
//! `Interpreter::TRACE_*` (`Mixfix/userLevelRewritingContext.cc`, `Mixfix/trial.cc`):
//!
//! | flag           | section it gates                                                          |
//! |----------------|--------------------------------------------------------------------------|
//! | `master`       | everything (`set trace on/off`)                                          |
//! | `body`         | the `*********** <kind>` header + the `eq/mb/ceq …` body **and** (nested) the rewrite/membership substitution |
//! | `substitution` | the `Var --> binding` lines (rewrite/membership: also needs `body`; trial/fragment: standalone) |
//! | `rewrite`      | the redex / `--->` / result, and the membership `… becomes …` line       |
//! | `whole`        | the `Old:`/`New:` whole-term lines                                        |
//! | `condition`    | events recorded *inside* a condition (`depth > 0`) — the nested reductions |
//! | `eq` / `mb` / `builtin` | whether equation / membership / built-in steps trace at all      |

use tnk_core::dag::DagId;
use tnk_core::engine::{RewriteKind, StmtKind, TraceEvent};
use tnk_core::sort::SortId;
use tnk_core::term::{ConditionFragment, Term};
use tnk_frontend::lex::Interner;
use tnk_frontend::pretty::{print_pretty, print_term};
use tnk_frontend::sig::syntax::{BuiltModule, EqTrace, MbTrace, RlTrace};

/// Maude's trace line header (`UserLevelRewritingContext::header`): eleven `*` and a space.
const HEADER: &str = "*********** ";

/// The granular trace flags — Maude's `Interpreter::TRACE_*` sub-flags, set via `set trace [<option>]
/// on|off`. `master` is the bare `set trace on|off`; the rest default as Maude does (all on but `whole`).
#[derive(Clone, Copy)]
pub(crate) struct TraceFlags {
    /// `set trace on|off` — the master switch; when off, nothing is recorded or rendered.
    pub master: bool,
    pub body: bool,
    pub substitution: bool,
    pub rewrite: bool,
    pub whole: bool,
    pub condition: bool,
    pub eq: bool,
    pub mb: bool,
    /// `set trace rls` — whether rule (`rl`/`crl`) steps trace at all (Maude's `TRACE_RL`). Pillar A.
    pub rl: bool,
    pub builtin: bool,
}

impl Default for TraceFlags {
    fn default() -> Self {
        // Maude defaults (interpreter.hh:137): every section on except `whole`; the master starts off
        // (`set trace on` turns it on).
        TraceFlags {
            master: false,
            body: true,
            substitution: true,
            rewrite: true,
            whole: false,
            condition: true,
            eq: true,
            mb: true,
            rl: true,
            builtin: true,
        }
    }
}

impl TraceFlags {
    /// Apply `set trace [<option>] on|off`; `args` is the words after `trace`. Returns the error message
    /// on bad syntax / an unsupported option (rule/strategy/select options are a Phase-2-of-project item).
    pub(crate) fn apply(&mut self, args: &[&str]) -> Result<(), String> {
        let (opt, val) = match args {
            [v] => (None, *v),
            [o, v] => (Some(*o), *v),
            _ => return Err("set trace: expected `[<option>] on|off`.".into()),
        };
        let on = match val {
            "on" => true,
            "off" => false,
            _ => return Err(format!("set trace: expected `on` or `off`, got `{val}`.")),
        };
        match opt {
            None => self.master = on,
            Some("condition") => self.condition = on,
            Some("whole") => self.whole = on,
            Some("substitution") => self.substitution = on,
            Some("rewrite") => self.rewrite = on,
            Some("body") => self.body = on,
            Some("builtin") => self.builtin = on,
            Some("eqs") => self.eq = on,
            Some("mbs") => self.mb = on,
            Some("rls") => self.rl = on,
            Some(o) => {
                return Err(format!(
                    "set trace: unsupported option `{o}` \
                     (supported: condition, whole, substitution, rewrite, body, builtin, eqs, mbs, rls)."
                ));
            }
        }
        Ok(())
    }

    /// Whether a statement of `kind` traces at all (Maude's `TRACE_EQ` / `TRACE_MB`).
    fn stmt_enabled(&self, kind: StmtKind) -> bool {
        match kind {
            StmtKind::Equation => self.eq,
            StmtKind::Membership => self.mb,
            StmtKind::Rule => self.rl,
        }
    }
}

/// Render the recorded [`TraceEvent`] stream to Maude's trace text under `flags`. Empty when nothing
/// traced. The caller has already ensured recording matched `flags.master` (events are empty when off).
pub(crate) fn render_trace(
    m: &BuiltModule,
    i: &Interner,
    events: &[TraceEvent],
    flags: TraceFlags,
    color: bool,
) -> String {
    let mut r = Renderer { m, i, flags, color, out: String::new(), trial_counter: 0, trial_stack: Vec::new() };
    for ev in events {
        r.event(ev);
    }
    r.out
}

/// Render a rule's body (`rl lhs => rhs .`) from `rl_traces[rule_id]` — used by `show path` /
/// `show search graph` to annotate a state-graph arc. Reuses the trace body rendering.
pub(crate) fn rule_body(m: &BuiltModule, i: &Interner, rule_id: u32, color: bool) -> String {
    let r = Renderer {
        m,
        i,
        flags: TraceFlags::default(),
        color,
        out: String::new(),
        trial_counter: 0,
        trial_stack: Vec::new(),
    };
    r.rl_body(&m.rl_traces[rule_id as usize])
}

struct Renderer<'a> {
    m: &'a BuiltModule,
    i: &'a Interner,
    flags: TraceFlags,
    color: bool,
    out: String,
    /// Maude's per-command `trialCount` (reset each reduce): incremented on each *rendered* trial start.
    trial_counter: u32,
    /// Open (rendered) trial numbers, innermost last — so a `success/failure #N` pairs with its start
    /// across nesting (a condition may contain nested trials).
    trial_stack: Vec<u32>,
}

impl Renderer<'_> {
    /// Dispatch one event: gate it (by `condition` depth + the kind flag), manage the trial counter /
    /// stack, and append the rendered text. Only this method mutates `self.out`/`self.trial_*`; the
    /// per-kind helpers below are pure (`&self -> String`), which keeps the borrows simple.
    fn event(&mut self, ev: &TraceEvent) {
        // `set trace condition off`: events recorded inside a condition (depth > 0) are dropped, mirroring
        // Maude's `CONDITION_EVAL` sub-context trace flag. Applies uniformly to every event kind, so a
        // trial's start and end (same depth) are dropped together — the trial stack stays balanced.
        if ev.depth() > 0 && !self.flags.condition {
            return;
        }
        match ev {
            TraceEvent::Rewrite { kind, eq_id, redex, result, bindings, whole_before, whole_after, .. } => {
                let text = match kind {
                    RewriteKind::Equation if self.flags.eq => self.rewrite_eq(
                        eq_id.expect("equation rewrite has an id"),
                        *redex,
                        *result,
                        bindings,
                        *whole_before,
                        *whole_after,
                    ),
                    RewriteKind::BuiltIn if self.flags.builtin => {
                        self.rewrite_builtin(*redex, *result, *whole_before, *whole_after)
                    }
                    RewriteKind::Rule if self.flags.rl => self.rewrite_rule(
                        eq_id.expect("rule rewrite has an id"),
                        *redex,
                        *result,
                        bindings,
                        *whole_before,
                        *whole_after,
                    ),
                    _ => return,
                };
                self.out.push_str(&text);
            }
            TraceEvent::Membership { mb_id, subject, old_sort, new_sort, bindings, whole, .. } => {
                if self.flags.mb {
                    let text = self.membership(*mb_id, *subject, *old_sort, *new_sort, bindings, *whole);
                    self.out.push_str(&text);
                }
            }
            TraceEvent::TrialStart { kind, stmt_id, bindings, .. } => {
                if self.flags.stmt_enabled(*kind) {
                    self.trial_counter += 1;
                    let n = self.trial_counter;
                    self.trial_stack.push(n);
                    let text = self.trial_start(*kind, *stmt_id, n, bindings);
                    self.out.push_str(&text);
                }
            }
            TraceEvent::TrialEnd { kind, success, .. } => {
                if self.flags.stmt_enabled(*kind)
                    && let Some(n) = self.trial_stack.pop()
                {
                    let word = if *success { "success" } else { "failure" };
                    self.out.push_str(&format!("{HEADER}{word} #{n}\n"));
                }
            }
            TraceEvent::FragmentStart { kind, stmt_id, index, first_attempt, .. } => {
                if self.flags.stmt_enabled(*kind) {
                    let text = self.fragment_start(*kind, *stmt_id, *index, *first_attempt);
                    self.out.push_str(&text);
                }
            }
            TraceEvent::FragmentEnd { kind, stmt_id, index, success, bindings, .. } => {
                if self.flags.stmt_enabled(*kind) {
                    let text = self.fragment_end(*kind, *stmt_id, *index, *success, bindings);
                    self.out.push_str(&text);
                }
            }
        }
    }

    // ---- equation / built-in rewrites (Maude `tracePreEqRewrite` + `tracePostEqRewrite`) ----

    fn rewrite_eq(&self, eq_id: u32, redex: DagId, result: DagId, bindings: &[Option<DagId>], whole_before: Option<DagId>, whole_after: Option<DagId>) -> String {
        let eqt = &self.m.eq_traces[eq_id as usize];
        let mut s = String::new();
        if self.flags.body {
            s.push_str(HEADER);
            s.push_str("equation\n");
            s.push_str(&self.eq_body(eqt));
            s.push('\n');
            if self.flags.substitution {
                s.push_str(&self.substitution(&eqt.var_names, bindings));
            }
        } else {
            // No statement labels yet, so always the unlabeled form.
            s.push_str("(unlabeled equation)\n");
        }
        s.push_str(&self.rewrite_tail(redex, result, whole_before, whole_after));
        s
    }

    /// A rule step (Maude `tracePreRuleRewrite` + `tracePostRuleRewrite`): `*********** rule` + the rule
    /// body + substitution + the `redex ---> result` tail — the rewrite counterpart of [`rewrite_eq`].
    fn rewrite_rule(&self, rule_id: u32, redex: DagId, result: DagId, bindings: &[Option<DagId>], whole_before: Option<DagId>, whole_after: Option<DagId>) -> String {
        let rlt = &self.m.rl_traces[rule_id as usize];
        let mut s = String::new();
        if self.flags.body {
            s.push_str(HEADER);
            s.push_str("rule\n");
            s.push_str(&self.rl_body(rlt));
            s.push('\n');
            if self.flags.substitution {
                s.push_str(&self.substitution(&rlt.var_names, bindings));
            }
        } else {
            s.push_str("(unlabeled rule)\n");
        }
        s.push_str(&self.rewrite_tail(redex, result, whole_before, whole_after));
        s
    }

    fn rewrite_builtin(&self, redex: DagId, result: DagId, whole_before: Option<DagId>, whole_after: Option<DagId>) -> String {
        let mut s = String::new();
        if self.flags.body {
            s.push_str(HEADER);
            s.push_str("equation\n");
        }
        // The `(built-in equation for symbol …)` line is NOT body-gated (Maude prints it for equation==0
        // regardless). The symbol is the redex's top symbol's canonical (mixfix) name, e.g. `_+_`.
        let name = self.m.engine.symbol(self.m.engine.node(redex).symbol()).name();
        s.push_str(&format!("(built-in equation for symbol {name})\n"));
        s.push_str(&self.rewrite_tail(redex, result, whole_before, whole_after));
        s
    }

    /// The shared `[Old:] redex ---> result [New:]` tail of an equation/built-in step.
    fn rewrite_tail(&self, redex: DagId, result: DagId, whole_before: Option<DagId>, whole_after: Option<DagId>) -> String {
        let mut s = String::new();
        if self.flags.whole && let Some(w) = whole_before {
            s.push_str(&format!("Old: {}\n", self.dag(w)));
        }
        if self.flags.rewrite {
            s.push_str(&format!("{}\n--->\n{}\n", self.dag(redex), self.dag(result)));
        }
        if self.flags.whole && let Some(w) = whole_after {
            s.push_str(&format!("New: {}\n", self.dag(w)));
        }
        s
    }

    // ---- membership axioms (Maude `tracePreScApplication`) ----

    fn membership(&self, mb_id: u32, subject: DagId, old_sort: SortId, new_sort: SortId, bindings: &[Option<DagId>], whole: Option<DagId>) -> String {
        let mbt = &self.m.mb_traces[mb_id as usize];
        let mut s = String::new();
        if self.flags.body {
            s.push_str(HEADER);
            s.push_str("membership axiom\n");
            s.push_str(&self.mb_body(mbt));
            s.push('\n');
            if self.flags.substitution {
                s.push_str(&self.substitution(&mbt.var_names, bindings));
            }
        } else {
            s.push_str("(unlabeled membership axiom)\n");
        }
        // `whole` for a membership is Maude's `Whole:` line; we don't reconstruct it (memberships fire at
        // node construction, off the reduce frame stack), so it is `None` — documented limitation.
        if self.flags.whole && let Some(w) = whole {
            s.push_str(&format!("Whole: {}\n", self.dag(w)));
        }
        if self.flags.rewrite {
            let sorts = self.m.engine.sorts();
            s.push_str(&format!("{}: {} becomes {}\n", sorts.name(old_sort), self.dag(subject), sorts.name(new_sort)));
        }
        s
    }

    // ---- conditional sub-stream (Maude `trial.cc`) ----

    fn trial_start(&self, kind: StmtKind, stmt_id: u32, n: u32, bindings: &[Option<DagId>]) -> String {
        let (body, var_names) = self.stmt_body(kind, stmt_id);
        let mut s = format!("{HEADER}trial #{n}\n{body}\n");
        // Trial substitution is gated by `substitution` alone (not nested under `body`, unlike a rewrite).
        if self.flags.substitution {
            s.push_str(&self.substitution(var_names, bindings));
        }
        s
    }

    fn fragment_start(&self, kind: StmtKind, stmt_id: u32, index: u32, first_attempt: bool) -> String {
        let prefix = if first_attempt { "" } else { "re-" };
        format!("{HEADER}{prefix}solving condition fragment\n{}\n", self.fragment_text(kind, stmt_id, index))
    }

    fn fragment_end(&self, kind: StmtKind, stmt_id: u32, index: u32, success: bool, bindings: &[Option<DagId>]) -> String {
        let word = if success { "success" } else { "failure" };
        let mut s = format!("{HEADER}{word} for condition fragment\n{}\n", self.fragment_text(kind, stmt_id, index));
        if success && self.flags.substitution {
            s.push_str(&self.substitution(self.stmt_var_names(kind, stmt_id), bindings));
        }
        s
    }

    // ---- shared body / fragment / substitution rendering (pure: `&self -> String`) ----

    /// The statement's source body line (no header) — `[c]eq …` or `[c]mb …`. Used by both the rewrite
    /// step and the trial.
    fn stmt_body(&self, kind: StmtKind, stmt_id: u32) -> (String, &[String]) {
        match kind {
            StmtKind::Equation => {
                let eqt = &self.m.eq_traces[stmt_id as usize];
                (self.eq_body(eqt), &eqt.var_names)
            }
            StmtKind::Membership => {
                let mbt = &self.m.mb_traces[stmt_id as usize];
                (self.mb_body(mbt), &mbt.var_names)
            }
            StmtKind::Rule => {
                let rlt = &self.m.rl_traces[stmt_id as usize];
                (self.rl_body(rlt), &rlt.var_names)
            }
        }
    }

    fn stmt_var_names(&self, kind: StmtKind, stmt_id: u32) -> &[String] {
        match kind {
            StmtKind::Equation => &self.m.eq_traces[stmt_id as usize].var_names,
            StmtKind::Membership => &self.m.mb_traces[stmt_id as usize].var_names,
            StmtKind::Rule => &self.m.rl_traces[stmt_id as usize].var_names,
        }
    }

    /// `[c]eq lhs = rhs [if cond] [\[owise\]] .`
    fn eq_body(&self, eqt: &EqTrace) -> String {
        let kw = if eqt.condition.is_empty() { "eq" } else { "ceq" };
        let mut s = format!("{kw} {} = {}", self.term(&eqt.lhs, &eqt.var_names), self.term(&eqt.rhs, &eqt.var_names));
        if !eqt.condition.is_empty() {
            s.push_str(&format!(" if {}", self.condition(&eqt.condition, &eqt.var_names)));
        }
        if eqt.owise {
            s.push_str(" [owise]");
        }
        s.push_str(" .");
        s
    }

    /// `[c]mb lhs : sort [if cond] .`
    fn mb_body(&self, mbt: &MbTrace) -> String {
        let kw = if mbt.condition.is_empty() { "mb" } else { "cmb" };
        let mut s = format!("{kw} {} : {}", self.term(&mbt.lhs, &mbt.var_names), self.m.engine.sorts().name(mbt.sort));
        if !mbt.condition.is_empty() {
            s.push_str(&format!(" if {}", self.condition(&mbt.condition, &mbt.var_names)));
        }
        s.push_str(" .");
        s
    }

    /// `[c]rl [\[label\] :] lhs => rhs [if cond] .`
    fn rl_body(&self, rlt: &RlTrace) -> String {
        let kw = if rlt.condition.is_empty() { "rl" } else { "crl" };
        let label = match &rlt.label {
            Some(l) => format!(" [{l}] :"),
            None => String::new(),
        };
        let mut s = format!(
            "{kw}{label} {} => {}",
            self.term(&rlt.lhs, &rlt.var_names),
            self.term(&rlt.rhs, &rlt.var_names)
        );
        if !rlt.condition.is_empty() {
            s.push_str(&format!(" if {}", self.condition(&rlt.condition, &rlt.var_names)));
        }
        s.push_str(" .");
        s
    }

    /// The `index`-th condition fragment of a statement, on its own (the `solving/success/failure
    /// condition fragment` line).
    fn fragment_text(&self, kind: StmtKind, stmt_id: u32, index: u32) -> String {
        let (cond, var_names): (&[ConditionFragment], &[String]) = match kind {
            StmtKind::Equation => {
                let eqt = &self.m.eq_traces[stmt_id as usize];
                (&eqt.condition, &eqt.var_names)
            }
            StmtKind::Membership => {
                let mbt = &self.m.mb_traces[stmt_id as usize];
                (&mbt.condition, &mbt.var_names)
            }
            StmtKind::Rule => {
                let rlt = &self.m.rl_traces[stmt_id as usize];
                (&rlt.condition, &rlt.var_names)
            }
        };
        self.fragment(&cond[index as usize], var_names)
    }

    /// A condition (the `if` clause): fragments joined by ` /\ `.
    fn condition(&self, cond: &[ConditionFragment], var_names: &[String]) -> String {
        cond.iter().map(|f| self.fragment(f, var_names)).collect::<Vec<_>>().join(" /\\ ")
    }

    /// One condition fragment: `lhs = rhs` / `term : sort` / `pattern := subject`.
    fn fragment(&self, frag: &ConditionFragment, var_names: &[String]) -> String {
        match frag {
            ConditionFragment::Equality { lhs, rhs } => {
                format!("{} = {}", self.term(lhs, var_names), self.term(rhs, var_names))
            }
            ConditionFragment::SortTest { term, sort } => {
                format!("{} : {}", self.term(term, var_names), self.m.engine.sorts().name(*sort))
            }
            ConditionFragment::Matching { pattern, subject, .. } => {
                format!("{} := {}", self.term(pattern, var_names), self.term(subject, var_names))
            }
        }
    }

    /// `Var --> binding` lines (Maude `printSubstitution`): each variable in index order, `(unbound)` for
    /// an unbound fresh `:=` variable, or `empty substitution` when the statement has no variables.
    fn substitution(&self, var_names: &[String], bindings: &[Option<DagId>]) -> String {
        if bindings.is_empty() {
            return "empty substitution\n".to_string();
        }
        let mut s = String::new();
        for (k, b) in bindings.iter().enumerate() {
            let name = var_names.get(k).map(String::as_str).unwrap_or("?");
            match b {
                Some(d) => s.push_str(&format!("{name} --> {}\n", self.dag(*d))),
                None => s.push_str(&format!("{name} --> (unbound)\n")),
            }
        }
        s
    }

    /// Render a runtime DAG node (redex/result/binding/whole) — Maude-faithful, colored per the flag.
    fn dag(&self, d: DagId) -> String {
        print_pretty(self.m, self.i, d, self.color)
    }

    /// Render a static pattern `Term` (a body / fragment), with its statement's variable names.
    fn term(&self, t: &Term, var_names: &[String]) -> String {
        print_term(self.m, self.i, t, var_names, self.color)
    }
}
