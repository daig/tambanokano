//! Local synchronous META-INTERPRETER manager.
//!
//! The parent scheduler yields an owned [`MetaEnvelope`]. Child computation happens only after the
//! parent-engine borrow has ended; replies cross back as another envelope. Every child owns an independent
//! Session, persistent reflection transport, module/view catalog, operation cursors, and nested registry.

use std::collections::{HashMap, VecDeque};

use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::descent::{DescentOps, MetaCtx};
use tnk_core::external::{
    ExternalResponse, ExternalRewriteBreakdown, ExternalTargetToken, MetaEnvelope, MetaNode,
    MetaNodeRef, MetaTransport,
};
use tnk_core::symbol::{MetaHooks, MetaOp};
use tnk_frontend::lex::Interner;
use tnk_modules::db::ModuleDb;
use tnk_modules::meta::{MetaDescent, down_term, up_parsed_term, up_sort};
use tnk_modules::view::ViewDb;

use super::Session;

/// Response constructors not guaranteed to occur in the request graph or META hook table. They are
/// predeclared in each private transport so protocol callbacks can build them by name and arity.
const RESPONSE_OPS: &[(&str, usize, bool)] = &[
    ("true", 0, false),
    ("false", 0, false),
    ("upModule", 2, false),
    ("interpreter", 1, false),
    ("createdInterpreter", 3, true),
    ("insertedModule", 2, true),
    ("insertedView", 2, true),
    ("showingModule", 3, true),
    ("showingView", 3, true),
    ("printedTerm", 3, true),
    ("printedTermToString", 3, true),
    ("parsedTerm", 3, true),
    ("gotLesserSorts", 3, true),
    ("gotMaximalSorts", 3, true),
    ("gotMinimalSorts", 3, true),
    ("comparedTypes", 5, true),
    ("gotKind", 3, true),
    ("gotKinds", 3, true),
    ("gotGlbTypes", 3, true),
    ("gotMaximalAritySet", 3, true),
    ("normalizedTerm", 4, true),
    ("reducedTerm", 5, true),
    ("rewroteTerm", 5, true),
    ("frewroteTerm", 5, true),
    ("erewroteTerm", 5, true),
    ("srewroteTerm", 5, true),
    ("gotSearchResult", 6, true),
    ("gotSearchResultAndPath", 7, true),
    ("gotMatch", 4, true),
    ("gotXmatch", 5, true),
    ("appliedRule", 6, true),
    ("appliedRule", 7, true),
    ("gotUnifier", 4, true),
    ("gotDisjointUnifier", 5, true),
    ("gotIrredundantUnifier", 4, true),
    ("gotIrredundantDisjointUnifier", 5, true),
    ("gotVariant", 8, true),
    ("gotVariantUnifier", 5, true),
    ("gotDisjointVariantUnifier", 6, true),
    ("gotVariantMatcher", 4, true),
    ("gotOneStepNarrowing", 10, true),
    ("gotNarrowingSearchResult", 9, true),
    ("gotNarrowingSearchResultAndPath", 9, true),
    ("noSuchResult", 3, true),
    ("noSuchResult", 4, true),
    ("bye", 2, true),
    ("interpreterError", 3, true),
];

#[derive(Default)]
pub(super) struct InterpreterRegistry {
    children: HashMap<u64, LocalInterpreter>,
}

struct LocalInterpreter {
    session: Box<Session>,
    transport: MetaTransport,
    target: MetaEnvelope,
    target_token: Option<ExternalTargetToken>,
    modules: HashMap<String, MetaEnvelope>,
    views: HashMap<String, MetaEnvelope>,
    cursors: VecDeque<CursorEntry>,
}

struct CursorEntry {
    key: String,
    index: u64,
    cumulative_rewrites: u64,
}

/// Parent-engine actions are returned as owned data. Session applies registration changes only after this
/// handler has returned, so no child operation can run while the parent engine is borrowed.
pub(super) struct ManagerAction {
    pub response: Option<ExternalResponse>,
    pub register: Option<(u64, MetaEnvelope)>,
    pub unregister: Option<ExternalTargetToken>,
}

impl ManagerAction {
    fn rejected() -> Self {
        Self {
            response: None,
            register: None,
            unregister: None,
        }
    }

    fn reply(response: ExternalResponse) -> Self {
        Self {
            response: Some(response),
            register: None,
            unregister: None,
        }
    }
}

pub(super) struct LocalInterpreterManager<'a> {
    registry: &'a mut InterpreterRegistry,
    source_interner: &'a Interner,
    source_db: &'a ModuleDb,
    source_views: &'a ViewDb,
}

impl<'a> LocalInterpreterManager<'a> {
    pub(super) fn new(
        registry: &'a mut InterpreterRegistry,
        source_interner: &'a Interner,
        source_db: &'a ModuleDb,
        source_views: &'a ViewDb,
    ) -> Self {
        Self {
            registry,
            source_interner,
            source_db,
            source_views,
        }
    }

    pub(super) fn handle(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(target) = request.root(0) else {
            return ManagerAction::rejected();
        };
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let name = request.name(message).to_string();
        let args = request.children(message);
        if request.name(target) == "interpreterManager" {
            if name == "createInterpreter" && args.len() == 3 && request.name(args[2]) == "none" {
                return self.create(request);
            }
            // Malformed create/manager traffic is not consumed by the reference.
            return ManagerAction::rejected();
        }

        let Some(id) = interpreter_id(&request, target) else {
            return ManagerAction::rejected();
        };
        if name == "quit" {
            if args.len() != 2 {
                return ManagerAction::rejected();
            }
            return self.quit(id, request);
        }
        let Some(child) = self.registry.children.get_mut(&id) else {
            // Stale children are normally filtered by the parent capability registry. If one reaches this
            // point because its target was concurrently invalidated, leave the message untouched.
            return ManagerAction::rejected();
        };
        child.handle(request)
    }

    pub(super) fn commit_registration(&mut self, id: u64, token: ExternalTargetToken) -> bool {
        let Some(child) = self.registry.children.get_mut(&id) else {
            return false;
        };
        child.target_token = Some(token);
        true
    }

    pub(super) fn rollback_create(&mut self, id: u64) {
        self.registry.children.remove(&id);
    }

    fn create(&mut self, request: MetaEnvelope) -> ManagerAction {
        let id = (0..).find(|candidate| !self.registry.children.contains_key(candidate));
        let Some(id) = id else {
            return ManagerAction::rejected();
        };
        let mut transport = MetaTransport::new(&request, RESPONSE_OPS);
        let transaction = transport.transact(&[&request], |ctx, _, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let manager = *args.first()?;
            let requester = *args.get(1)?;
            let child = make_interpreter_id(ctx, id)?;
            let reply = response(ctx, "createdInterpreter", vec![requester, manager, child])?;
            Some(((), Some(reply)))
        });
        let Some(((), Some(reply))) = transaction else {
            return ManagerAction::rejected();
        };
        let Some(reply_root) = reply.root(0) else {
            return ManagerAction::rejected();
        };
        let Some(&target_node) = reply.children(reply_root).get(2) else {
            return ManagerAction::rejected();
        };
        let target = reply.rooted_at(target_node);
        let mut session = Session::new();
        session.interner = self.source_interner.clone();
        session.db = self.source_db.clone();
        session.views = self.source_views.clone();
        self.registry.children.insert(
            id,
            LocalInterpreter {
                session: Box::new(session),
                transport,
                target: target.clone(),
                target_token: None,
                modules: HashMap::new(),
                views: HashMap::new(),
                cursors: VecDeque::new(),
            },
        );
        ManagerAction {
            response: Some(ExternalResponse {
                reply: Some(reply),
                rewrites: 0,
                breakdown: ExternalRewriteBreakdown::default(),
            }),
            register: Some((id, target)),
            unregister: None,
        }
    }

    fn quit(&mut self, id: u64, request: MetaEnvelope) -> ManagerAction {
        let Some(child) = self.registry.children.get_mut(&id) else {
            return ManagerAction::rejected();
        };
        let transaction = child.transport.transact(&[&request], |ctx, _, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let target = *args.first()?;
            let requester = *args.get(1)?;
            let reply = response(ctx, "bye", vec![requester, target])?;
            Some(((), Some(reply)))
        });
        let Some(((), Some(reply))) = transaction else {
            return ManagerAction::rejected();
        };
        let token = child.target_token;
        self.registry.children.remove(&id);
        ManagerAction {
            response: Some(ExternalResponse {
                reply: Some(reply),
                rewrites: 0,
                breakdown: ExternalRewriteBreakdown::default(),
            }),
            register: None,
            unregister: token,
        }
    }
}

impl LocalInterpreter {
    fn handle(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let name = request.name(message).to_string();
        match name.as_str() {
            "insertModule" => self.insert_module(request),
            "insertView" => self.insert_view(request),
            "showModule" => self.show_module(request),
            "showView" => self.show_view(request),
            _ if module_argument_index(&name).is_some() => self.module_operation(request, &name),
            _ => self.error(request, "Unsupported message."),
        }
    }

    fn insert_module(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let Some(&module_node) = request.children(message).get(2) else {
            return ManagerAction::rejected();
        };
        let source = request.rooted_at(module_node);
        let source_is_deferred = source
            .root(0)
            .is_some_and(|root| source.name(root) == "upModule");
        let LocalInterpreter {
            session,
            transport,
            modules,
            cursors,
            ..
        } = self;
        let transaction = transport.transact(&[&request], |ctx, hooks, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let target = *args.first()?;
            let requester = *args.get(1)?;
            let module = *args.get(2)?;
            let name = reflected_module_name(ctx, module)?;

            let decoded = {
                let mut descent = MetaDescent::new(
                    &mut session.interner,
                    &session.db,
                    &session.views,
                    &mut session.meta_state,
                );
                descent.down_module_with_source(ctx, hooks, module)
            };

            let reply = response(ctx, "insertedModule", vec![requester, target])?;
            Some(((name, decoded), Some(reply)))
        });
        let Some(((name, decoded), Some(reply))) = transaction else {
            return self.error(request, "Bad module.");
        };
        let mut diagnostics = String::new();
        let (stored_source, rewrites) = match decoded {
            Some((module_source, loaded)) => {
                // Preserve the exact engine produced by reflected down-translation. The source enters
                // the child's ModuleDb for import/dependency resolution; dependents still rebuild from
                // that source, while this module retains every statement accepted by `downSignature`.
                session.enter_meta_module(module_source, loaded, &mut diagnostics);
                (source, u64::from(source_is_deferred))
            }
            None => {
                let Some(module_source) = session.db.get(&name).cloned() else {
                    return self.error(request, "Bad module.");
                };
                // A flat `upModule` can contain builtin `special`/`poly` declarations that are not
                // reconstructible as ordinary surface attributes. Keep an equivalent non-flat form:
                // the module's own declarations stay reflected while builtin declarations arrive through
                // the cloned source imports each time a META handler down-translates it.
                let normalized = transport.transact(&[], |ctx, hooks, _| {
                    let qid = ctx.make_na(
                        *hooks.ops.get("qidSymbol")?,
                        NaValue::Qid(name.clone().into()),
                    );
                    let false_symbol = ctx.resolve_op("false", 0)?;
                    let flat = ctx.app(false_symbol, Vec::new());
                    let (module, _) =
                        invoke_descent(session, ctx, hooks, MetaOp::UpModule, vec![qid, flat])?;
                    Some(((), Some(module)))
                });
                let Some(((), Some(normalized))) = normalized else {
                    return self.error(request, "Bad module.");
                };
                session.enter_module(module_source, &mut diagnostics);
                (normalized, u64::from(source_is_deferred))
            }
        };
        let own_error = format!("error in module `{name}`:");
        if diagnostics.lines().any(|line| line.starts_with(&own_error)) {
            return self.error(request, "Bad module.");
        }
        modules.insert(name, stored_source);
        cursors.clear();
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites,
            breakdown: ExternalRewriteBreakdown::default(),
        })
    }

    fn insert_view(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let Some(&view_node) = request.children(message).get(2) else {
            return ManagerAction::rejected();
        };
        let source = request.rooted_at(view_node);
        let LocalInterpreter {
            session,
            transport,
            views,
            cursors,
            ..
        } = self;
        let transaction = transport.transact(&[&request], |ctx, hooks, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let target = *args.first()?;
            let requester = *args.get(1)?;
            let view = *args.get(2)?;
            let decoded = {
                let mut descent = MetaDescent::new(
                    &mut session.interner,
                    &session.db,
                    &session.views,
                    &mut session.meta_state,
                );
                descent.down_view(ctx, hooks, view)
            }?;
            let name = decoded.name.clone();
            let reply = response(ctx, "insertedView", vec![requester, target])?;
            Some(((name, decoded), Some(reply)))
        });
        let Some(((name, decoded), Some(reply))) = transaction else {
            return self.error(request, "Bad view.");
        };

        let mut diagnostics = String::new();
        session.enter_view(decoded, &mut diagnostics);
        if diagnostics.lines().any(|line| line.starts_with("error")) {
            return self.error(request, "Bad view.");
        }
        views.insert(name, source);
        cursors.clear();
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites: 0,
            breakdown: ExternalRewriteBreakdown::default(),
        })
    }

    fn show_module(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let args = request.children(message);
        let Some(name) = args.get(2).and_then(|&node| request.qid(node)) else {
            return self.error(request, "Bad module name.");
        };
        let Some(module) = self.modules.get(name).cloned() else {
            return self.error(request, "Nonexistent module.");
        };
        let transaction = self
            .transport
            .transact(&[&request, &module], |ctx, _, roots| {
                let message = *roots.first()?.get(1)?;
                let args = ctx.children(message);
                let target = *args.first()?;
                let requester = *args.get(1)?;
                let module = *roots.get(1)?.first()?;
                let reply = response(ctx, "showingModule", vec![requester, target, module])?;
                Some(((), Some(reply)))
            });
        let Some(((), Some(reply))) = transaction else {
            return ManagerAction::rejected();
        };
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites: 0,
            breakdown: ExternalRewriteBreakdown::default(),
        })
    }

    fn show_view(&mut self, request: MetaEnvelope) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let args = request.children(message);
        let Some(name) = args.get(2).and_then(|&node| request.qid(node)) else {
            return self.error(request, "Bad view name.");
        };
        let Some(view) = self.views.get(name).cloned() else {
            return self.error(request, "Nonexistent view.");
        };
        let transaction = self
            .transport
            .transact(&[&request, &view], |ctx, _, roots| {
                let message = *roots.first()?.get(1)?;
                let args = ctx.children(message);
                let target = *args.first()?;
                let requester = *args.get(1)?;
                let view = *roots.get(1)?.first()?;
                let reply = response(ctx, "showingView", vec![requester, target, view])?;
                Some(((), Some(reply)))
            });
        let Some(((), Some(reply))) = transaction else {
            return ManagerAction::rejected();
        };
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites: 0,
            breakdown: ExternalRewriteBreakdown::default(),
        })
    }

    fn module_operation(&mut self, request: MetaEnvelope, name: &str) -> ManagerAction {
        let Some(message) = request.root(1) else {
            return ManagerAction::rejected();
        };
        let args = request.children(message);
        let module_index = module_argument_index(name).expect("caller checked operation");
        let Some(module_name) = args.get(module_index).and_then(|&node| request.qid(node)) else {
            return self.error(request, "Bad module name.");
        };
        let Some(module) = self.modules.get(module_name).cloned() else {
            return self.error(request, "Nonexistent module.");
        };
        let cursor = cursor_spec(&request, message, name);
        // A nonzero apply cursor proves that the preceding child rule result was consumed by the
        // parent's protocol rule. Maude transfers that completed child rule into the breakdown only
        // at this continuation boundary; the aggregate was already transferred with its reply.
        let completed_apply_rule = matches!(name, "applyRule" | "xapplyRule")
            && cursor.as_ref().is_some_and(|c| c.index > 0);
        let module_name = module_name.to_string();
        let LocalInterpreter {
            session,
            transport,
            cursors,
            ..
        } = self;
        let transaction = transport.transact(&[&request, &module], |ctx, hooks, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let module = *roots.get(1)?.first()?;
            let target = *args.first()?;
            let requester = *args.get(1)?;
            let mut breakdown = ExternalRewriteBreakdown::default();
            let before = ctx.rewrite_breakdown();
            let result = handle_module_operation(
                session,
                cursors,
                cursor.as_ref(),
                ctx,
                hooks,
                name,
                &module_name,
                module,
                &args,
                requester,
                target,
                &mut breakdown,
            )?;
            let after = ctx.rewrite_breakdown();
            breakdown.membership_applications += after.0.saturating_sub(before.0);
            breakdown.rule_rewrites += after.1.saturating_sub(before.1);
            breakdown.variant_narrowing_steps += after.2.saturating_sub(before.2);
            breakdown.narrowing_steps += after.3.saturating_sub(before.3);
            Some(((result.0, breakdown), Some(result.1)))
        });
        let Some(((rewrites, mut breakdown), Some(reply))) = transaction else {
            return self.error(request, operation_error(name));
        };
        breakdown.rule_rewrites += u64::from(completed_apply_rule);
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites,
            breakdown,
        })
    }

    fn error(&mut self, request: MetaEnvelope, text: &str) -> ManagerAction {
        let transaction = self.transport.transact(&[&request], |ctx, hooks, roots| {
            let message = *roots.first()?.get(1)?;
            let args = ctx.children(message);
            let target = *args.first()?;
            let requester = *args.get(1)?;
            let text = ctx.make_na(
                *hooks.ops.get("stringSymbol")?,
                NaValue::Str(text.as_bytes().into()),
            );
            let reply = response(ctx, "interpreterError", vec![requester, target, text])?;
            Some(((), Some(reply)))
        });
        let Some(((), Some(reply))) = transaction else {
            return ManagerAction::rejected();
        };
        ManagerAction::reply(ExternalResponse {
            reply: Some(reply),
            rewrites: 0,
            breakdown: ExternalRewriteBreakdown::default(),
        })
    }
}

fn handle_module_operation(
    session: &mut Session,
    cursors: &mut VecDeque<CursorEntry>,
    cursor: Option<&CursorSpec>,
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    name: &str,
    module_name: &str,
    module: DagId,
    args: &[DagId],
    requester: DagId,
    target: DagId,
    breakdown: &mut ExternalRewriteBreakdown,
) -> Option<(u64, DagId)> {
    // A source-backed insertion already has the authoritative module in the child's database. Feed
    // META descent an unreduced `upModule` reference so `MetaDescent::down_module` takes its lossless
    // source path instead of round-tripping the reflected declaration DAG. Hand-written inserted modules
    // are absent from the database and continue through the ordinary down-translation path.
    let source_module = if session.db.get(module_name).is_some() {
        let qid = ctx.make_na(
            *hooks.ops.get("qidSymbol")?,
            NaValue::Qid(module_name.into()),
        );
        let false_ = ctx.app(ctx.resolve_op("false", 0)?, Vec::new());
        let deferred = ctx.app(ctx.resolve_op("upModule", 2)?, vec![qid, false_]);
        Some(ctx.root(deferred))
    } else {
        None
    };
    let module = if name == "srewriteTerm" {
        module
    } else {
        source_module.as_ref().map_or(module, |root| root.get())
    };
    match name {
        "reduceTerm" => {
            let (work, term, type_) =
                session.reduce_meta_term(ctx, hooks, module_name, *args.get(3)?)?;
            counted_reply(
                ctx,
                "reducedTerm",
                requester,
                target,
                work,
                work,
                vec![term, type_],
            )
        }
        "normalizeTerm" => {
            let (term, type_) =
                session.normalize_meta_term(ctx, hooks, module_name, *args.get(3)?)?;
            Some((
                0,
                response(ctx, "normalizedTerm", vec![requester, target, term, type_])?,
            ))
        }
        "rewriteTerm" => {
            let bound = down_bound(ctx, *args.get(2)?)?;
            let (work, operation_breakdown, term, type_) = session.rewrite_meta_term(
                ctx,
                hooks,
                module_name,
                *args.get(4)?,
                DirectRewrite::Rule,
                bound,
                1,
            )?;
            *breakdown = operation_breakdown;
            counted_reply(
                ctx,
                "rewroteTerm",
                requester,
                target,
                work,
                work,
                vec![term, type_],
            )
        }
        "frewriteTerm" | "erewriteTerm" => {
            let bound = down_bound(ctx, *args.get(2)?)?;
            let gas = nat(ctx, *args.get(3)?)?;
            if gas == 0 {
                return None;
            }
            let mode = if name == "frewriteTerm" {
                DirectRewrite::Position
            } else {
                DirectRewrite::Object
            };
            let (work, operation_breakdown, term, type_) = session.rewrite_meta_term(
                ctx,
                hooks,
                module_name,
                *args.get(5)?,
                mode,
                bound,
                gas,
            )?;
            *breakdown = operation_breakdown;
            let reply_name = if name == "frewriteTerm" {
                "frewroteTerm"
            } else {
                "erewroteTerm"
            };
            counted_reply(
                ctx,
                reply_name,
                requester,
                target,
                work,
                work,
                vec![term, type_],
            )
        }
        "parseTerm" => {
            let (result, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::Parse,
                vec![module, *args.get(3)?, *args.get(4)?, *args.get(5)?],
            )?;
            Some((
                0,
                response(ctx, "parsedTerm", vec![requester, target, result])?,
            ))
        }
        "printTerm" | "printTermToString" => {
            let op = if name == "printTerm" {
                MetaOp::PrettyPrint
            } else {
                MetaOp::PrintToString
            };
            let (result, _) = invoke_descent(
                session,
                ctx,
                hooks,
                op,
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                ],
            )?;
            let reply = if name == "printTerm" {
                "printedTerm"
            } else {
                "printedTermToString"
            };
            Some((0, response(ctx, reply, vec![requester, target, result])?))
        }
        "getLesserSorts" | "getMaximalSorts" | "getMinimalSorts" | "getKind" => {
            let (op, reply) = match name {
                "getLesserSorts" => (MetaOp::LesserSorts, "gotLesserSorts"),
                "getMaximalSorts" => (MetaOp::MaximalSorts, "gotMaximalSorts"),
                "getMinimalSorts" => (MetaOp::MinimalSorts, "gotMinimalSorts"),
                _ => (MetaOp::GetKind, "gotKind"),
            };
            let (result, _) = invoke_descent(session, ctx, hooks, op, vec![module, *args.get(3)?])?;
            Some((0, response(ctx, reply, vec![requester, target, result])?))
        }
        "getKinds" => {
            // A source-backed insertion arrived as `upModule(Q, true)`. Query the sort graph reconstructed
            // from that flat reflected signature: its ACU SubsortDeclSet order is observable in multi-top
            // kind names and can differ from the source module's native declaration order.
            let reflected = if session.db.get(module_name).is_some() {
                let qid = ctx.make_na(
                    *hooks.ops.get("qidSymbol")?,
                    NaValue::Qid(module_name.into()),
                );
                let true_ = ctx.app(ctx.resolve_op("true", 0)?, Vec::new());
                let (flat, _) =
                    invoke_descent(session, ctx, hooks, MetaOp::UpModule, vec![qid, true_])?;
                Some(ctx.root(flat))
            } else {
                None
            };
            let query_module = reflected.as_ref().map_or(module, |root| root.get());
            let (result, _) =
                invoke_descent(session, ctx, hooks, MetaOp::GetKinds, vec![query_module])?;
            Some((
                0,
                response(ctx, "gotKinds", vec![requester, target, result])?,
            ))
        }
        "compareTypes" => {
            let first = *args.get(3)?;
            let second = *args.get(4)?;
            let (same, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::SameKind,
                vec![module, first, second],
            )?;
            // Each descent may allocate and collect in the private transport engine. Pin earlier Boolean
            // results until the three-result protocol reply owns them; otherwise a recycled `DagId` can
            // silently turn `comparedTypes(...)` into a non-message and leave the request unreduced.
            let same = ctx.root(same);
            let (forward, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::SortLeq,
                vec![module, first, second],
            )?;
            let forward = ctx.root(forward);
            let (backward, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::SortLeq,
                vec![module, second, first],
            )?;
            Some((
                0,
                response(
                    ctx,
                    "comparedTypes",
                    vec![requester, target, same.get(), forward.get(), backward],
                )?,
            ))
        }
        "getGlbTypes" => {
            let set = *args.get(3)?;
            let mut call = vec![module];
            if ctx.name(ctx.top(set)) != "none" {
                let types = ctx.children(set);
                if types.is_empty() {
                    call.push(set);
                } else {
                    call.extend(types);
                }
            }
            let (result, _) = invoke_descent(session, ctx, hooks, MetaOp::GlbSorts, call)?;
            Some((
                0,
                response(ctx, "gotGlbTypes", vec![requester, target, result])?,
            ))
        }
        "getMaximalAritySet" => {
            let (result, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::MaximalAritySet,
                vec![module, *args.get(3)?, *args.get(4)?, *args.get(5)?],
            )?;
            Some((
                0,
                response(ctx, "gotMaximalAritySet", vec![requester, target, result])?,
            ))
        }
        "getMatch" => {
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::Match,
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                ],
            )?;
            let (reported, transfer) = account_cursor(cursors, cursor?, work, false);
            if ctx.name(ctx.top(result)).starts_with("noMatch") {
                return no_such_count(ctx, requester, target, reported, transfer, None);
            }
            counted_reply(
                ctx,
                "gotMatch",
                requester,
                target,
                reported,
                transfer,
                vec![result],
            )
        }
        "getXmatch" => {
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::Xmatch,
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                    *args.get(7)?,
                    *args.get(8)?,
                ],
            )?;
            let (reported, transfer) = account_cursor(cursors, cursor?, work, false);
            let children = ctx.children(result);
            if children.len() != 2 {
                return no_such_count(ctx, requester, target, reported, transfer, None);
            }
            counted_reply(
                ctx,
                "gotXmatch",
                requester,
                target,
                reported,
                transfer,
                children,
            )
        }
        "applyRule" => {
            let extension = args.len() == 9;
            let op = if extension {
                MetaOp::Xapply
            } else {
                MetaOp::Apply
            };
            let mut call = vec![module];
            call.extend_from_slice(&args[3..]);
            let (result, work) = invoke_descent(session, ctx, hooks, op, call)?;
            // `RewriteSearchState::transferCountTo` resets the cached state's counters after every
            // reply. Each application therefore reports and transfers this request's work directly;
            // it is not a cumulative recomputation to subtract through `account_cursor`.
            let _ = cursor?;
            let (reported, transfer) = (work, work);
            let children = ctx.children(result);
            let expected = if extension { 4 } else { 3 };
            if children.len() != expected {
                return no_such_count(ctx, requester, target, reported, transfer, None);
            }
            counted_reply(
                ctx,
                "appliedRule",
                requester,
                target,
                reported,
                transfer,
                children,
            )
        }
        "getSearchResult" | "getSearchResultAndPath" => {
            let call = vec![
                module,
                *args.get(3)?,
                *args.get(4)?,
                *args.get(5)?,
                *args.get(6)?,
                *args.get(7)?,
                *args.get(8)?,
            ];
            let (result, work) = invoke_descent(session, ctx, hooks, MetaOp::Search, call.clone())?;
            let (_, transfer) = account_cursor(cursors, cursor?, work, false);
            let reported = transfer;
            let children = ctx.children(result);
            if children.len() != 3 {
                return no_such_count(ctx, requester, target, reported, transfer, None);
            }
            let mut payload = children;
            let reply = if name == "getSearchResultAndPath" {
                let checkpoint = ctx.rewrites();
                let (trace, _) = invoke_descent(session, ctx, hooks, MetaOp::SearchPath, call)?;
                ctx.restore_rewrites(checkpoint);
                payload.push(trace);
                "gotSearchResultAndPath"
            } else {
                "gotSearchResult"
            };
            counted_reply(ctx, reply, requester, target, reported, transfer, payload)
        }
        "getUnifier"
        | "getDisjointUnifier"
        | "getIrredundantUnifier"
        | "getIrredundantDisjointUnifier" => {
            let disjoint = name.contains("Disjoint");
            let irredundant = name.contains("Irredundant");
            let (result, _) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::Unify {
                    disjoint,
                    irredundant,
                    legacy: false,
                },
                vec![module, *args.get(3)?, *args.get(4)?, *args.get(5)?],
            )?;
            let result_name = ctx.name(ctx.top(result));
            let children = ctx.children(result);
            if result_name.contains("noUnifier") || children.is_empty() {
                let complete = make_bool(ctx, !result_name.contains("Incomplete"))?;
                return Some((
                    0,
                    response(ctx, "noSuchResult", vec![requester, target, complete])?,
                ));
            }
            let reply = match name {
                "getUnifier" => "gotUnifier",
                "getDisjointUnifier" => "gotDisjointUnifier",
                "getIrredundantUnifier" => "gotIrredundantUnifier",
                _ => "gotIrredundantDisjointUnifier",
            };
            let mut reply_args = vec![requester, target];
            reply_args.extend(children);
            Some((0, response(ctx, reply, reply_args)?))
        }
        "getVariant" => {
            let irredundant = bool_value(ctx, *args.get(5)?)?;
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::GetVariant {
                    irredundant,
                    legacy: false,
                },
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(6)?,
                    *args.get(7)?,
                ],
            )?;
            symbolic_counted_result(
                cursors,
                cursor?,
                ctx,
                requester,
                target,
                result,
                work,
                "gotVariant",
                5,
            )
        }
        "getVariantUnifier" | "getDisjointVariantUnifier" => {
            let disjoint = name == "getDisjointVariantUnifier";
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::VariantUnify {
                    disjoint,
                    legacy: false,
                },
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                    *args.get(7)?,
                ],
            )?;
            symbolic_counted_result(
                cursors,
                cursor?,
                ctx,
                requester,
                target,
                result,
                work,
                if disjoint {
                    "gotDisjointVariantUnifier"
                } else {
                    "gotVariantUnifier"
                },
                if disjoint { 3 } else { 2 },
            )
        }
        "getVariantMatcher" => {
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::VariantMatch,
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                    *args.get(7)?,
                ],
            )?;
            let top = ctx.top(result);
            let failure = if Some(top) == hooks.ops.get("noMatchSubstSymbol").copied() {
                Some(true)
            } else if Some(top) == hooks.ops.get("noMatchIncompleteSubstSymbol").copied() {
                Some(false)
            } else {
                None
            };
            symbolic_counted_whole_result(
                cursors,
                cursor?,
                ctx,
                requester,
                target,
                result,
                work,
                "gotVariantMatcher",
                failure,
            )
        }
        "getOneStepNarrowing" => {
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::NarrowingApply,
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                    *args.get(7)?,
                ],
            )?;
            symbolic_counted_result(
                cursors,
                cursor?,
                ctx,
                requester,
                target,
                result,
                work,
                "gotOneStepNarrowing",
                7,
            )
        }
        "getNarrowingSearchResult" | "getNarrowingSearchResultAndPath" => {
            let path = name.ends_with("AndPath");
            let (result, work) = invoke_descent(
                session,
                ctx,
                hooks,
                MetaOp::NarrowingSearch { path },
                vec![
                    module,
                    *args.get(3)?,
                    *args.get(4)?,
                    *args.get(5)?,
                    *args.get(6)?,
                    *args.get(7)?,
                    *args.get(8)?,
                    *args.get(9)?,
                ],
            )?;
            let children = ctx.children(result);
            let success = children.len() == 6;
            let (reported, transfer) = account_deferred_cursor(cursors, cursor?, work, success);
            if !success {
                let complete = !ctx.name(ctx.top(result)).contains("Incomplete");
                return no_such_count(ctx, requester, target, reported, transfer, Some(complete));
            }
            counted_reply(
                ctx,
                if path {
                    "gotNarrowingSearchResultAndPath"
                } else {
                    "gotNarrowingSearchResult"
                },
                requester,
                target,
                reported,
                transfer,
                children,
            )
        }
        "srewriteTerm" => {
            let depth_first = match ctx.name(ctx.top(*args.get(5)?)) {
                "depthFirst" => true,
                "breadthFirst" => false,
                _ => return None,
            };
            let (result, work) = invoke_srewrite_descent(
                session,
                ctx,
                hooks,
                module_name,
                depth_first,
                vec![module, *args.get(3)?, *args.get(4)?, *args.get(6)?],
            )?;
            let children = ctx.children(result);
            if children.len() != 2 {
                return no_such_count(ctx, requester, target, work, work, None);
            }
            counted_reply(ctx, "srewroteTerm", requester, target, work, work, children)
        }
        _ => None,
    }
}

fn invoke_descent(
    session: &mut Session,
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    op: MetaOp,
    args: Vec<DagId>,
) -> Option<(DagId, u64)> {
    let symbol = ctx.resolve_op(&format!("%externalCall{}", args.len()), args.len())?;
    let redex = ctx.app(symbol, args);
    let before = ctx.rewrites();
    let result = {
        let mut descent = MetaDescent::new(
            &mut session.interner,
            &session.db,
            &session.views,
            &mut session.meta_state,
        )
        .with_interpreter_manager_accounting();
        descent.descend(ctx, op, hooks, redex)?
    };
    Some((result, ctx.rewrites().saturating_sub(before)))
}

fn invoke_srewrite_descent(
    session: &mut Session,
    ctx: &mut MetaCtx,
    hooks: &MetaHooks,
    module_name: &str,
    depth_first: bool,
    args: Vec<DagId>,
) -> Option<(DagId, u64)> {
    let symbol = ctx.resolve_op(&format!("%externalCall{}", args.len()), args.len())?;
    let redex = ctx.app(symbol, args);
    let before = ctx.rewrites();
    let Session {
        interner,
        db,
        modules,
        views,
        meta_state,
        ..
    } = session;
    let strat_defs = &modules.get(module_name)?.built.strat_defs;
    let mut descent = MetaDescent::new(interner, db, views, meta_state);
    let result = descent.srewrite_with_strat_defs(ctx, hooks, redex, depth_first, strat_defs)?;
    Some((result, ctx.rewrites().saturating_sub(before)))
}

fn symbolic_counted_result(
    cursors: &mut VecDeque<CursorEntry>,
    cursor: &CursorSpec,
    ctx: &mut MetaCtx,
    requester: DagId,
    target: DagId,
    result: DagId,
    work: u64,
    reply: &str,
    expected_children: usize,
) -> Option<(u64, DagId)> {
    let (reported, transfer) = account_cursor(cursors, cursor, work, true);
    let children = ctx.children(result);
    if children.len() != expected_children {
        let complete = !ctx.name(ctx.top(result)).contains("Incomplete");
        return no_such_count(ctx, requester, target, reported, transfer, Some(complete));
    }
    counted_reply(ctx, reply, requester, target, reported, transfer, children)
}

fn symbolic_counted_whole_result(
    cursors: &mut VecDeque<CursorEntry>,
    cursor: &CursorSpec,
    ctx: &mut MetaCtx,
    requester: DagId,
    target: DagId,
    result: DagId,
    work: u64,
    reply: &str,
    failure_complete: Option<bool>,
) -> Option<(u64, DagId)> {
    let (reported, transfer) = account_cursor(cursors, cursor, work, true);
    if let Some(complete) = failure_complete {
        no_such_count(ctx, requester, target, reported, transfer, Some(complete))
    } else {
        counted_reply(
            ctx,
            reply,
            requester,
            target,
            reported,
            transfer,
            vec![result],
        )
    }
}

fn counted_reply(
    ctx: &mut MetaCtx,
    name: &str,
    requester: DagId,
    target: DagId,
    reported: u64,
    transferred: u64,
    payload: Vec<DagId>,
) -> Option<(u64, DagId)> {
    let count = make_nat(ctx, reported)?;
    let mut args = vec![requester, target, count];
    args.extend(payload);
    Some((transferred, response(ctx, name, args)?))
}

fn no_such_count(
    ctx: &mut MetaCtx,
    requester: DagId,
    target: DagId,
    reported: u64,
    transferred: u64,
    complete: Option<bool>,
) -> Option<(u64, DagId)> {
    let count = make_nat(ctx, reported)?;
    let mut args = vec![requester, target, count];
    if let Some(complete) = complete {
        args.push(make_bool(ctx, complete)?);
    }
    Some((transferred, response(ctx, "noSuchResult", args)?))
}

struct CursorSpec {
    key: String,
    index: u64,
}

fn cursor_spec(request: &MetaEnvelope, message: MetaNodeRef, name: &str) -> Option<CursorSpec> {
    if !matches!(
        name,
        "getSearchResult"
            | "getSearchResultAndPath"
            | "getMatch"
            | "getXmatch"
            | "applyRule"
            | "getVariant"
            | "getVariantUnifier"
            | "getDisjointVariantUnifier"
            | "getVariantMatcher"
            | "getOneStepNarrowing"
            | "getNarrowingSearchResult"
            | "getNarrowingSearchResultAndPath"
    ) {
        return None;
    }
    let args = request.children(message);
    let (&solution, key_args) = args.split_last()?;
    Some(CursorSpec {
        key: format!("{name}:{}", request.structural_key(&key_args[2..])),
        index: envelope_nat(request, solution)?,
    })
}

fn account_cursor(
    cursors: &mut VecDeque<CursorEntry>,
    spec: &CursorSpec,
    work: u64,
    internally_incremental: bool,
) -> (u64, u64) {
    if let Some(position) = cursors.iter().position(|entry| entry.key == spec.key) {
        let mut entry = cursors
            .remove(position)
            .expect("position came from cursor deque");
        let (reported, transferred) = if entry.index <= spec.index {
            if internally_incremental {
                (work, work)
            } else {
                (work, work.saturating_sub(entry.cumulative_rewrites))
            }
        } else {
            (work, work)
        };
        entry.index = spec.index;
        entry.cumulative_rewrites = reported;
        cursors.push_front(entry);
        return (reported, transferred);
    }
    if cursors.len() == 4 {
        cursors.pop_back();
    }
    cursors.push_front(CursorEntry {
        key: spec.key.clone(),
        index: spec.index,
        cumulative_rewrites: work,
    });
    (work, work)
}

fn account_deferred_cursor(
    cursors: &mut VecDeque<CursorEntry>,
    spec: &CursorSpec,
    work: u64,
    success: bool,
) -> (u64, u64) {
    let position = cursors.iter().position(|entry| entry.key == spec.key);
    let mut entry = position
        .map(|position| {
            cursors
                .remove(position)
                .expect("position came from cursor deque")
        })
        .unwrap_or_else(|| CursorEntry {
            key: spec.key.clone(),
            index: spec.index,
            cumulative_rewrites: 0,
        });
    let reported = if position.is_some() && entry.index <= spec.index {
        entry.cumulative_rewrites.saturating_add(work)
    } else {
        work
    };
    if success {
        entry.index = spec.index;
        entry.cumulative_rewrites = reported;
        if cursors.len() == 4 {
            cursors.pop_back();
        }
        cursors.push_front(entry);
        (reported, 0)
    } else {
        (reported, reported)
    }
}

fn module_argument_index(name: &str) -> Option<usize> {
    match name {
        "rewriteTerm" => Some(3),
        "frewriteTerm" | "erewriteTerm" => Some(4),
        "printTerm"
        | "printTermToString"
        | "parseTerm"
        | "getLesserSorts"
        | "getMaximalSorts"
        | "getMinimalSorts"
        | "compareTypes"
        | "getKind"
        | "getKinds"
        | "getGlbTypes"
        | "getMaximalAritySet"
        | "normalizeTerm"
        | "reduceTerm"
        | "srewriteTerm"
        | "getSearchResult"
        | "getSearchResultAndPath"
        | "getMatch"
        | "getXmatch"
        | "applyRule"
        | "getUnifier"
        | "getDisjointUnifier"
        | "getIrredundantUnifier"
        | "getIrredundantDisjointUnifier"
        | "getVariant"
        | "getVariantUnifier"
        | "getDisjointVariantUnifier"
        | "getVariantMatcher"
        | "getOneStepNarrowing"
        | "getNarrowingSearchResult"
        | "getNarrowingSearchResultAndPath" => Some(2),
        _ => None,
    }
}

fn operation_error(name: &str) -> &'static str {
    match name {
        "printTerm" | "printTermToString" => "Bad term.",
        "parseTerm" => "Bad token list.",
        "getLesserSorts" | "getMaximalSorts" | "getMinimalSorts" | "compareTypes" | "getKind"
        | "getKinds" | "getGlbTypes" | "getMaximalAritySet" => "Bad type.",
        "normalizeTerm" | "reduceTerm" => "Bad term.",
        "rewriteTerm" | "frewriteTerm" | "erewriteTerm" => "Bad limit.",
        "srewriteTerm" => "Bad strategy.",
        "getSearchResult" | "getSearchResultAndPath" => "Bad search.",
        "getMatch" | "getXmatch" | "getVariantMatcher" => "Bad matching problem.",
        "applyRule" => "Bad rule application.",
        "getUnifier"
        | "getDisjointUnifier"
        | "getIrredundantUnifier"
        | "getIrredundantDisjointUnifier"
        | "getVariantUnifier"
        | "getDisjointVariantUnifier" => "Bad unification problem.",
        "getVariant" => "Bad reducibility constraint.",
        "getOneStepNarrowing" => "Bad narrowing problem.",
        "getNarrowingSearchResult" | "getNarrowingSearchResultAndPath" => {
            "Bad narrowing search problem."
        }
        _ => "Unsupported message.",
    }
}

impl Session {
    fn reduce_meta_term(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        module: &str,
        subject: DagId,
    ) -> Option<(u64, DagId, DagId)> {
        let Session {
            modules,
            interner,
            db,
            views,
            meta_state,
            ..
        } = self;
        let loaded = modules.get_mut(module)?;
        let subject = down_term(ctx, hooks, subject, &mut loaded.built, interner)?;
        loaded.built.engine.reset_rewrites();
        let result = {
            let mut descent = MetaDescent::new(interner, db, views, meta_state);
            loaded.built.engine.reduce_with(subject, &mut descent)
        };
        let rewrites = loaded.built.engine.rewrites();
        let up_result = up_parsed_term(ctx, hooks, &loaded.built, interner, result);
        let up_type = up_sort(ctx, hooks, &loaded.built, result);
        Some((rewrites, up_result, up_type))
    }

    fn normalize_meta_term(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        module: &str,
        subject: DagId,
    ) -> Option<(DagId, DagId)> {
        let loaded = self.modules.get_mut(module)?;
        let subject = down_term(ctx, hooks, subject, &mut loaded.built, &mut self.interner)?;
        let result = loaded.built.engine.normalize_for_unify(subject);
        let up_result = up_parsed_term(ctx, hooks, &loaded.built, &self.interner, result);
        let up_type = up_sort(ctx, hooks, &loaded.built, result);
        Some((up_result, up_type))
    }

    fn rewrite_meta_term(
        &mut self,
        ctx: &mut MetaCtx,
        hooks: &MetaHooks,
        module: &str,
        subject: DagId,
        mode: DirectRewrite,
        bound: Option<u64>,
        gas: u64,
    ) -> Option<(u64, ExternalRewriteBreakdown, DagId, DagId)> {
        let Session {
            interner,
            db,
            modules,
            views,
            meta_state,
            interpreters,
            ..
        } = self;
        let loaded = modules.get_mut(module)?;
        let subject = down_term(ctx, hooks, subject, &mut loaded.built, interner)?;
        loaded.built.engine.reset_rewrites();
        let result = match mode {
            DirectRewrite::Rule => {
                let mut rewriting = loaded.built.engine.rewrite(subject);
                rewriting.run(&mut loaded.built.engine, bound).term
            }
            DirectRewrite::Position => {
                let mut rewriting = loaded.built.engine.frewrite(subject, gas);
                rewriting.run(&mut loaded.built.engine, bound).term
            }
            DirectRewrite::Object => {
                loaded.built.engine.reset_external();
                *interpreters = InterpreterRegistry::default();
                let mut rewriting = loaded.built.engine.erewrite(subject, gas);
                super::drive_external_rewriting(
                    &mut rewriting,
                    loaded,
                    interner,
                    db,
                    views,
                    meta_state,
                    interpreters,
                    bound,
                )
                .term
            }
        };
        let rewrites = loaded.built.engine.rewrites();
        let (membership_applications, rule_rewrites, variant_narrowing_steps, narrowing_steps) =
            loaded.built.engine.rewrite_breakdown();
        let breakdown = ExternalRewriteBreakdown {
            membership_applications,
            rule_rewrites,
            variant_narrowing_steps,
            narrowing_steps,
        };
        let up_result = up_parsed_term(ctx, hooks, &loaded.built, interner, result);
        let up_type = up_sort(ctx, hooks, &loaded.built, result);
        Some((rewrites, breakdown, up_result, up_type))
    }
}

#[derive(Clone, Copy)]
enum DirectRewrite {
    Rule,
    Position,
    Object,
}
fn response(ctx: &mut MetaCtx, name: &str, args: Vec<DagId>) -> Option<DagId> {
    let symbol = ctx.resolve_op(name, args.len())?;
    Some(ctx.app(symbol, args))
}

fn reflected_module_name(ctx: &MetaCtx, module: DagId) -> Option<String> {
    let header = *ctx.children(module).first()?;
    qid(ctx, header).or_else(|| qid(ctx, *ctx.children(header).first()?))
}

fn qid(ctx: &MetaCtx, node: DagId) -> Option<String> {
    match ctx.repr(node) {
        NodeRepr::Qid(value) => Some(value.to_string()),
        _ => None,
    }
}

fn interpreter_id(envelope: &MetaEnvelope, node: MetaNodeRef) -> Option<u64> {
    (envelope.name(node) == "interpreter")
        .then(|| envelope.children(node))?
        .first()
        .copied()
        .and_then(|id| envelope_nat(envelope, id))
}

fn envelope_nat(envelope: &MetaEnvelope, node: MetaNodeRef) -> Option<u64> {
    match envelope.node(node) {
        MetaNode::App { args, .. } if envelope.name(node) == "0" && args.is_empty() => Some(0),
        MetaNode::Iter { count, arg, .. } => {
            envelope_nat(envelope, *arg)?.checked_add(count.parse().ok()?)
        }
        _ => None,
    }
}

fn nat(ctx: &MetaCtx, node: DagId) -> Option<u64> {
    match ctx.repr(node) {
        NodeRepr::App if ctx.name(ctx.top(node)) == "0" && ctx.children(node).is_empty() => Some(0),
        NodeRepr::Iter { count, arg } => nat(ctx, arg)?.checked_add(count.parse().ok()?),
        _ => None,
    }
}

fn down_bound(ctx: &MetaCtx, node: DagId) -> Option<Option<u64>> {
    if ctx.name(ctx.top(node)) == "unbounded" {
        Some(None)
    } else {
        Some(Some(nat(ctx, node)?))
    }
}

fn make_nat(ctx: &mut MetaCtx, value: u64) -> Option<DagId> {
    let successor = ctx.resolve_op("s_", 1)?;
    let zero_symbol = ctx.resolve_op("0", 0)?;
    let zero = ctx.app(zero_symbol, Vec::new());
    Some(if value == 0 {
        zero
    } else {
        ctx.make_iter(successor, value, zero)
    })
}

fn make_interpreter_id(ctx: &mut MetaCtx, id: u64) -> Option<DagId> {
    let symbol = ctx.resolve_op("interpreter", 1)?;
    let id = make_nat(ctx, id)?;
    Some(ctx.app(symbol, vec![id]))
}

fn bool_value(ctx: &MetaCtx, node: DagId) -> Option<bool> {
    match ctx.name(ctx.top(node)) {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn make_bool(ctx: &mut MetaCtx, value: bool) -> Option<DagId> {
    let symbol = ctx.resolve_op(if value { "true" } else { "false" }, 0)?;
    Some(ctx.app(symbol, Vec::new()))
}
