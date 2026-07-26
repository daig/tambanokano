//! Resumable rewriting sessions — `rewrite` (rule-fair) and, from Pillar A-ii, `frewrite`
//! (position-fair).
//!
//! A [`Rewriting`] owns its current term (kept live by a [`RootGuard`]) and the round-robin rule
//! cursors, borrowing the [`Engine`] only per [`run`](Rewriting::run) call — so the REPL can store it
//! between commands to implement `continue`.

use crate::dag::DagId;
use crate::descent::{DescentOps, NullDescent};
use crate::engine::{ERewritePass, ERewritePassStep, Engine};
use crate::external::{ExternalRequestToken, ExternalResponse, MetaEnvelope};
use crate::root::RootGuard;
use crate::symbol::SymbolId;
use std::collections::HashMap;

/// The traversal discipline of a [`Rewriting`] session.
#[derive(Clone, Copy)]
enum Mode {
    /// `rewrite`: rule-fair — reduce to canonical, then apply the first rule at the top-down-first redex.
    RuleFair,
    /// `frewrite`: position-fair — `gas` rule applications per non-frozen position per traversal pass.
    PositionFair { gas: u64 },
    /// `erewrite`: object-message-fair — at a `config` soup, deliver queued messages object-by-object
    /// (Pillar 2.5-B); at any other node, fall back to position-fair. `gas` is the per-position gas for
    /// the non-config fallback (default 1).
    ObjectMessageFair { gas: u64 },
}

struct ObjectRunState {
    remaining: Option<u64>,
    pass: Option<ERewritePass>,
}

/// Result of driving an `erewrite` with host-owned external targets enabled.
pub enum ExternalRun {
    Complete(RewriteStep),
    Suspended {
        token: ExternalRequestToken,
        request: MetaEnvelope,
    },
}

/// A resumable rewriting session (`rewrite` or `frewrite`). Owns the current term — pinned by a
/// [`RootGuard`] so it survives GC across the reductions inside [`run`](Self::run) and while stored
/// between REPL `continue`s — and the per-symbol round-robin rule cursors (Maude's `RuleTable::nextRule`),
/// persisting across steps so a rewrite sequence cycles fairly through a symbol's rules.
pub struct Rewriting {
    current: DagId,
    root: RootGuard,
    cursors: HashMap<SymbolId, u32>,
    /// Set once a normal form is reached (no rule applies anywhere); a further `continue` is a no-op.
    done: bool,
    mode: Mode,
    object_run: Option<ObjectRunState>,
    next_external_request: u64,
    pending_external: Option<(ExternalRequestToken, MetaEnvelope)>,
}

/// The outcome of one bounded [`Rewriting::run`]: the current term, whether a normal form was reached
/// (`done`), and whether the term's least sort is known. `sort_known` is always `true` for `rewrite`
/// (every step ends on a `reduce`); a bounded `frewrite` stop will leave a non-canonical term whose
/// sort is not computed, so the REPL prints `result (sort not calculated): …` (A-ii).
pub struct RewriteStep {
    pub term: DagId,
    pub done: bool,
    pub sort_known: bool,
}

impl Rewriting {
    /// Construct a rule-fair (`rewrite`) session rooted at `current`.
    pub(crate) fn new_rule_fair(root: RootGuard, current: DagId) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::RuleFair,
            object_run: None,
            next_external_request: 0,
            pending_external: None,
        }
    }

    /// Construct a position-fair (`frewrite`) session rooted at `current`, with `gas` rule applications
    /// per position per pass.
    pub(crate) fn new_position_fair(root: RootGuard, current: DagId, gas: u64) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::PositionFair { gas },
            object_run: None,
            next_external_request: 0,
            pending_external: None,
        }
    }

    /// Construct an object-message-fair (`erewrite`) session rooted at `current` (Pillar 2.5-B), with
    /// `gas` for the non-config fallback.
    pub(crate) fn new_object_message_fair(root: RootGuard, current: DagId, gas: u64) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::ObjectMessageFair { gas },
            object_run: None,
            next_external_request: 0,
            pending_external: None,
        }
    }

    /// The current term.
    pub fn current(&self) -> DagId {
        self.current
    }

    /// Whether a normal form has been reached (no rule applies anywhere).
    pub fn is_done(&self) -> bool {
        self.done
    }
    /// Whether this session uses the EXTERNAL object-message scheduler.
    pub fn uses_external_messages(&self) -> bool {
        matches!(self.mode, Mode::ObjectMessageFair { .. })
    }

    /// Run up to `bound` rule applications (`None` = unbounded, to a normal form); `continue m` calls
    /// this again with `Some(m)`. Ordinary callers do not offer registered host targets.
    pub fn run(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
        if self.done {
            return self.completed_step();
        }
        match self.mode {
            Mode::RuleFair => self.run_rule_fair(engine, bound),
            Mode::PositionFair { gas } => self.run_position_fair(engine, bound, gas),
            Mode::ObjectMessageFair { gas } => {
                assert!(
                    self.pending_external.is_none(),
                    "a suspended external request must be resumed explicitly"
                );
                let mut descent = NullDescent;
                self.start_object_run(engine, bound, &mut descent);
                match self.drive_object_run(engine, gas, &mut descent, false) {
                    ExternalRun::Complete(step) => step,
                    ExternalRun::Suspended { .. } => {
                        unreachable!("host targets are disabled for Rewriting::run")
                    }
                }
            }
        }
    }

    /// Start or observe an `erewrite` run with registered host targets enabled. Reaching such a target
    /// returns an owned request and leaves the parent scheduler suspended. The caller must answer through
    /// [`resume_external`](Self::resume_external); calling this method again simply returns the same token
    /// and request.
    pub fn run_with_external(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        descent: &mut dyn DescentOps,
    ) -> ExternalRun {
        if self.done {
            return ExternalRun::Complete(self.completed_step());
        }
        if let Some((token, request)) = &self.pending_external {
            return ExternalRun::Suspended {
                token: *token,
                request: request.clone(),
            };
        }
        match self.mode {
            Mode::ObjectMessageFair { gas } => {
                self.start_object_run(engine, bound, descent);
                self.drive_object_run(engine, gas, descent, true)
            }
            _ => ExternalRun::Complete(self.run(engine, bound)),
        }
    }

    /// Resolve exactly the currently suspended external request, then continue the same pass and bound.
    /// `None` rejects the request and restores its message to the configuration. A stale/wrong token has
    /// no effect and returns `None`.
    pub fn resume_external(
        &mut self,
        engine: &mut Engine,
        token: ExternalRequestToken,
        response: Option<ExternalResponse>,
        descent: &mut dyn DescentOps,
    ) -> Option<ExternalRun> {
        let (pending, _) = self.pending_external.as_ref()?;
        if *pending != token {
            return None;
        }
        self.pending_external = None;
        let mut state = self.object_run.take()?;
        let pass = state.pass.as_mut()?;
        let accepted = response.is_some_and(|response| {
            engine.accept_external_response(
                response.reply.as_ref(),
                response.rewrites,
                response.breakdown,
            )
        });
        engine.resolve_erewrite_external(pass, accepted);
        self.object_run = Some(state);
        let Mode::ObjectMessageFair { gas } = self.mode else {
            unreachable!("only erewrite can suspend externally")
        };
        Some(self.drive_object_run(engine, gas, descent, true))
    }

    fn completed_step(&self) -> RewriteStep {
        RewriteStep {
            term: self.current,
            done: true,
            sort_known: true,
        }
    }

    /// `rewrite`: each step reduces `current` to canonical form (equationally — those rewrites count)
    /// then applies one rule at the top-down-first redex (Maude's `ruleRewrite`).
    fn run_rule_fair(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
        let mut steps = 0u64;
        loop {
            let reduced = engine.reduce(self.current);
            self.current = reduced;
            self.root.set(reduced);
            if bound == Some(steps) {
                return RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: true,
                };
            }
            match engine.rewrite_step(self.current, &mut self.cursors) {
                Some(next) => {
                    self.current = next;
                    self.root.set(next);
                    steps += 1;
                }
                None => {
                    self.done = true;
                    return RewriteStep {
                        term: self.current,
                        done: true,
                        sort_known: true,
                    };
                }
            }
        }
    }

    /// `frewrite`: position-fair. Reduce once, then repeat traversal passes (each gives every non-frozen
    /// position up to `gas` rule applications, reducing between) until the bound is hit or a pass makes
    /// no progress (a normal form). A bounded stop leaves a non-canonical term — `sort_known = false`, so
    /// the REPL prints `result (sort not calculated): …`, exactly as Maude does.
    fn run_position_fair(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        gas: u64,
    ) -> RewriteStep {
        let mut remaining = bound;
        self.current = engine.reduce(self.current);
        self.root.set(self.current);
        loop {
            let mut progress = false;
            let next = engine.frewrite_pass(
                self.current,
                gas,
                &mut remaining,
                &mut progress,
                &mut self.cursors,
            );
            self.current = next;
            self.root.set(next);
            if remaining == Some(0) {
                return RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: false,
                };
            }
            if !progress {
                self.done = true;
                return RewriteStep {
                    term: self.current,
                    done: true,
                    sort_known: true,
                };
            }
        }
    }

    /// Start one resumable object-message run. Initialization happens once even if a pass suspends.
    fn start_object_run(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        descent: &mut dyn DescentOps,
    ) {
        if self.object_run.is_some() {
            return;
        }
        self.current = engine.reduce_with(self.current, descent);
        self.root.set(self.current);
        self.object_run = Some(ObjectRunState {
            remaining: bound,
            pass: None,
        });
    }

    /// Drive the active object-message run to a bounded/final result or one external safe point.
    fn drive_object_run(
        &mut self,
        engine: &mut Engine,
        gas: u64,
        descent: &mut dyn DescentOps,
        offer_external: bool,
    ) -> ExternalRun {
        let mut state = self
            .object_run
            .take()
            .expect("object-message run must be initialized");
        loop {
            if state.remaining == Some(0) {
                return ExternalRun::Complete(RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: true,
                });
            }

            if engine.is_config_node(self.current) {
                if state.pass.is_none() {
                    state.pass = Some(engine.begin_erewrite_pass(self.current));
                }
                let pass_step = engine.advance_erewrite_pass(
                    state.pass.as_mut().expect("pass was created"),
                    &mut self.cursors,
                    offer_external,
                    descent,
                );
                match pass_step {
                    ERewritePassStep::External { target, message } => {
                        let request = engine
                            .with_meta_ctx(|ctx| MetaEnvelope::capture(ctx, &[target, message]));
                        let Some(request) = request else {
                            engine.resolve_erewrite_external(
                                state.pass.as_mut().expect("pass is suspended"),
                                false,
                            );
                            continue;
                        };
                        let token = ExternalRequestToken(self.next_external_request);
                        self.next_external_request = self
                            .next_external_request
                            .checked_add(1)
                            .expect("external request token space exhausted");
                        self.pending_external = Some((token, request.clone()));
                        self.object_run = Some(state);
                        return ExternalRun::Suspended { token, request };
                    }
                    ERewritePassStep::Complete { term, progress } => {
                        self.current = engine.reduce_with(term, descent);
                        self.root.set(self.current);
                        state.pass = None;
                        if !progress {
                            self.done = true;
                            return ExternalRun::Complete(self.completed_step());
                        }
                        if let Some(remaining) = &mut state.remaining {
                            *remaining -= 1;
                        }
                    }
                }
            } else {
                let mut progress = false;
                let next = engine.frewrite_pass(
                    self.current,
                    gas,
                    &mut state.remaining,
                    &mut progress,
                    &mut self.cursors,
                );
                self.current = engine.reduce_with(next, descent);
                self.root.set(self.current);
                if state.remaining == Some(0) {
                    return ExternalRun::Complete(RewriteStep {
                        term: self.current,
                        done: false,
                        sort_known: true,
                    });
                }
                if !progress {
                    self.done = true;
                    return ExternalRun::Complete(self.completed_step());
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::external::ExternalRewriteBreakdown;
    use crate::symbol::{MetaHooks, MetaOp, SpecialOp};
    use std::rc::Rc;

    #[test]
    fn external_request_continuation_and_target_teardown_survive_gc() {
        let mut engine = Engine::new();
        let configuration = engine.add_sort("Configuration");
        engine.close_sorts();

        let none = engine.add_op("none", vec![], configuration);
        let soup = engine.add_op_ac(
            "__",
            vec![configuration, configuration],
            configuration,
            Some(none),
        );
        engine.set_oo_flags(soup, true, false, false, false);
        let portal = engine.add_op("<>", vec![], configuration);
        engine.set_oo_flags(portal, false, false, false, true);
        let target = engine.add_op("child", vec![], configuration);
        let requester = engine.add_op("requester", vec![], configuration);
        let request = engine.add_op("request", vec![configuration, configuration], configuration);
        engine.set_oo_flags(request, false, false, true, false);
        let meta_hook = engine.add_op("%meta-hook", vec![], configuration);
        engine.set_special(
            meta_hook,
            SpecialOp::Meta {
                op: MetaOp::Deferred,
                hooks: Rc::new(MetaHooks::default()),
            },
        );
        engine.prepare_identities();

        let target_node = engine.make_const(target);
        let target_envelope = engine
            .with_meta_ctx(|ctx| MetaEnvelope::capture(ctx, &[target_node]))
            .expect("a ground target with META hooks is transportable");
        let registration = engine
            .register_external_target(&target_envelope)
            .expect("the transport target rebuilds in its source engine");

        let requester_node = engine.make_const(requester);
        let message = engine.make_node(request, vec![target_node, requester_node]);
        let portal_node = engine.make_const(portal);
        let initial = engine.make_acu(soup, vec![(portal_node, 1), (message, 1)]);
        let mut rewriting = engine.erewrite(initial, 1);
        let mut descent = NullDescent;

        let (token, captured) =
            match rewriting.run_with_external(&mut engine, Some(1), &mut descent) {
                ExternalRun::Suspended { token, request } => (token, request),
                ExternalRun::Complete(_) => panic!("registered target must suspend"),
            };
        assert_eq!(captured.root_count(), 2);

        engine.gc([]);
        let repeated = match rewriting.run_with_external(&mut engine, Some(1), &mut descent) {
            ExternalRun::Suspended { token, request } => (token, request),
            ExternalRun::Complete(_) => panic!("pending request must remain suspended"),
        };
        assert_eq!(repeated.0, token);
        assert_eq!(
            repeated.1.structural_key(&[
                repeated.1.root(0).expect("target root"),
                repeated.1.root(1).expect("message root"),
            ]),
            captured.structural_key(&[
                captured.root(0).expect("target root"),
                captured.root(1).expect("message root"),
            ])
        );

        assert!(
            rewriting
                .resume_external(
                    &mut engine,
                    ExternalRequestToken(token.0 + 1),
                    None,
                    &mut descent,
                )
                .is_none(),
            "a stale token cannot consume the pending request"
        );
        engine.gc([]);

        let response = ExternalResponse {
            reply: None,
            rewrites: 7,
            breakdown: ExternalRewriteBreakdown {
                membership_applications: 1,
                rule_rewrites: 2,
                variant_narrowing_steps: 1,
                narrowing_steps: 1,
            },
        };
        let step = match rewriting
            .resume_external(&mut engine, token, Some(response), &mut descent)
            .expect("the live token resumes")
        {
            ExternalRun::Complete(step) => step,
            ExternalRun::Suspended { .. } => panic!("the sole request was consumed"),
        };
        assert_eq!(engine.rewrites(), 7);
        assert_eq!(engine.rewrite_breakdown(), (1, 2, 1, 1));

        engine.gc([]);
        let live_with_target = engine.live_nodes();
        assert!(engine.unregister_external_target(registration));
        assert!(!engine.unregister_external_target(registration));
        assert!(engine.gc([]) > 0, "teardown releases the registered target");
        assert!(
            engine.live_nodes() < live_with_target,
            "the retained parent does not keep the detached target alive"
        );
        assert_eq!(engine.node(step.term).symbol(), portal);
        assert_eq!(rewriting.current(), step.term);
    }
}
