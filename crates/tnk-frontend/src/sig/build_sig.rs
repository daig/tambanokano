//! `build_module`: drive the `tnk-core` `Engine`'s constructor API from a [`PreModule`], and record the
//! frontend's [`SymbolSyntax`] / name→id tables. Order is forced by three kernel contracts: sorts closed
//! before ops; **all** op declarations before any node is built; `special` hooks resolved to ids. So:
//! sorts → close → **pass A** declare every op (theory-dispatched) + record syntax → **pass A2** record the
//! built-in anchors (succ/zero/string/float/qid) once all names resolve → **pass B** attach
//! ctor/strat/special. Statements are left raw (parsed in B4.4, which needs the grammar).

use crate::lex::{Interner, Token, split_mixfix};
use crate::sig::syntax::{BuiltModule, SymbolSyntax};
use crate::surface::ast::{Attrs, PreModule, SpecialSpec};
use std::collections::HashMap;
use tnk_core::engine::Engine;
use tnk_core::sort::SortId;
use tnk_core::symbol::{
    BoolHooks, FltOp, NatHooks, NumOp, SpecialOp, StrOp, SymbolId,
};

type R<T> = Result<T, String>;

/// The canonical mixfix name of an op (its name tokens concatenated): `[s_]`→`"s_"`, `[<_, ,, _>]`→`"<_,_>"`.
fn canonical_name(name: &[Token], i: &Interner) -> String {
    name.iter().map(|t| i.resolve(t.sym)).collect()
}

pub fn build_module(pm: &PreModule, interner: &mut Interner) -> R<BuiltModule> {
    let mut engine = Engine::new();
    let mut sorts: HashMap<String, SortId> = HashMap::new();

    // 1. Sorts + subsorts, then close.
    for name in &pm.sorts {
        let id = engine.add_sort(name.clone());
        sorts.insert(name.clone(), id);
    }
    let sort_id = |sorts: &HashMap<String, SortId>, name: &str| -> R<SortId> {
        sorts.get(name).copied().ok_or_else(|| format!("unknown sort `{name}`"))
    };
    for chain in &pm.subsorts {
        for w in chain.windows(2) {
            for sub in &w[0] {
                for sup in &w[1] {
                    engine.add_subsort(sort_id(&sorts, sub)?, sort_id(&sorts, sup)?);
                }
            }
        }
    }
    engine.close_sorts();

    let mut ops: HashMap<(String, usize), SymbolId> = HashMap::new();
    let mut name_to_sym: HashMap<String, SymbolId> = HashMap::new();
    let mut syntax: HashMap<SymbolId, SymbolSyntax> = HashMap::new();

    // Pass A: declare every op (theory-dispatched), record name→id + syntax.
    for od in &pm.ops {
        let cname = canonical_name(&od.name, interner);
        let arity = od.domain.len();
        let domain: Vec<SortId> =
            od.domain.iter().map(|s| sort_id(&sorts, s)).collect::<R<_>>()?;
        let range = sort_id(&sorts, &od.range)?;

        let sym = if let Some(&existing) = ops.get(&(cname.clone(), arity)) {
            engine.add_op_decl(existing, domain.clone(), range); // overload / `ditto`
            existing
        } else {
            let sym = declare_op(&mut engine, &cname, &od.attrs, &domain, range, &name_to_sym, interner)?;
            ops.insert((cname.clone(), arity), sym);
            name_to_sym.entry(cname.clone()).or_insert(sym);
            let frags = split_mixfix(&cname, interner);
            syntax.insert(
                sym,
                SymbolSyntax {
                    frags,
                    domain: domain.clone(),
                    range,
                    prec: od.attrs.prec,
                    gather: od.attrs.gather.clone(),
                },
            );
            sym
        };
        let _ = sym;
    }

    // Pass A2: record the built-in anchors (now every name resolves).
    let mut nat_succ = None;
    let mut nat_zero = None;
    let mut string_sym = None;
    let mut float_sym = None;
    let mut qid_sym = None;
    let mut succ_zero: HashMap<SymbolId, SymbolId> = HashMap::new();
    for od in &pm.ops {
        let Some(spec) = &od.attrs.special else { continue };
        let Some((class, _)) = &spec.id_hook else { continue };
        let cname = canonical_name(&od.name, interner);
        let arity = od.domain.len();
        let sym = ops[&(cname, arity)];
        match class.as_str() {
            "SuccSymbol" => {
                nat_succ = Some(sym);
                let zero = term_hook_sym(spec, "zeroTerm", &name_to_sym, interner)
                    .ok_or("SuccSymbol missing its zeroTerm")?;
                nat_zero = Some(zero);
                succ_zero.insert(sym, zero);
            }
            "StringSymbol" => string_sym = Some(sym),
            "FloatSymbol" => float_sym = Some(sym),
            "QuotedIdentifierSymbol" => qid_sym = Some(sym),
            _ => {}
        }
    }

    // Pass B: attach ctor / strat / special.
    for od in &pm.ops {
        if od.attrs.ditto {
            continue; // attributes inherited from the prior declaration (shared symbol)
        }
        let cname = canonical_name(&od.name, interner);
        let arity = od.domain.len();
        let sym = ops[&(cname, arity)];
        if od.attrs.ctor {
            engine.set_ctor(sym);
        }
        if let Some(strat) = &od.attrs.strat {
            engine.set_strategy(sym, strat);
        }
        if let Some(spec) = &od.attrs.special
            && let Some(op) = special_op(spec, arity, &name_to_sym, &succ_zero, interner)?
        {
            engine.set_special(sym, op);
        }
    }

    Ok(BuiltModule {
        engine,
        name: pm.name.clone(),
        sorts,
        ops,
        syntax,
        statements: Vec::new(), // moved in by the caller (B4.4); kept out of `&PreModule`
        nat_succ,
        nat_zero,
        string_sym,
        float_sym,
        qid_sym,
    })
}

/// Declare one operator via the kernel constructor for its theory (from the attribute flags).
fn declare_op(
    engine: &mut Engine,
    name: &str,
    attrs: &Attrs,
    domain: &[SortId],
    range: SortId,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> R<SymbolId> {
    // `id: <const>` — resolve the (already-declared) identity constant by name (the subset's `id:` is a
    // single constant).
    let identity = match &attrs.id {
        Some(toks) => {
            let first = toks.first().ok_or("empty id: term")?;
            Some(*name_to_sym.get(i.resolve(first.sym)).ok_or("unknown id: constant")?)
        }
        None => None,
    };
    Ok(if attrs.iter {
        engine.add_op_iter(name.to_string(), domain.to_vec(), range)
    } else if attrs.assoc && attrs.comm {
        engine.add_op_ac(name.to_string(), domain.to_vec(), range, identity)
    } else if attrs.assoc {
        engine.add_op_au(name.to_string(), domain.to_vec(), range, identity)
    } else if attrs.comm {
        engine.add_op_cui(name.to_string(), domain.to_vec(), range, attrs.idem, identity)
    } else {
        engine.add_op(name.to_string(), domain.to_vec(), range)
    })
}

// ---- hook resolution ----

fn op_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, sig) = spec.op_hooks.iter().find(|(p, _)| p == purpose)?;
    name_to_sym.get(i.resolve(sig.first()?.sym)).copied()
}

fn term_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, term) = spec.term_hooks.iter().find(|(p, _)| p == purpose)?;
    name_to_sym.get(i.resolve(term.first()?.sym)).copied()
}

fn nat_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> R<NatHooks> {
    let succ = op_hook_sym(spec, "succSymbol", name_to_sym, i).ok_or("missing op-hook succSymbol")?;
    let zero = succ_zero.get(&succ).copied().ok_or("succSymbol has no recorded zeroTerm")?;
    let minus = op_hook_sym(spec, "minusSymbol", name_to_sym, i);
    Ok(NatHooks { succ, zero, minus })
}

fn bool_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<BoolHooks> {
    Some(BoolHooks {
        true_: term_hook_sym(spec, "trueTerm", name_to_sym, i)?,
        false_: term_hook_sym(spec, "falseTerm", name_to_sym, i)?,
    })
}

/// Map a `special` directive to a kernel [`SpecialOp`] (or `None` for the pure NA-constant / successor
/// markers, which carry no reduction rule — their behaviour is the theory / the literal productions).
fn special_op(
    spec: &SpecialSpec,
    arity: usize,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> R<Option<SpecialOp>> {
    let Some((class, data)) = &spec.id_hook else { return Ok(None) };
    let code = data.first().map(String::as_str);
    let op = match class.as_str() {
        // Markers (no reduction rule).
        "SuccSymbol" | "StringSymbol" | "FloatSymbol" | "QuotedIdentifierSymbol" => return Ok(None),
        "MinusSymbol" => SpecialOp::Minus { nat: nat_hooks(spec, name_to_sym, succ_zero, i)? },
        "DivisionSymbol" => SpecialOp::Division { nat: nat_hooks(spec, name_to_sym, succ_zero, i)? },
        "EqualitySymbol" => SpecialOp::Equality {
            eq: term_hook_sym(spec, "equalTerm", name_to_sym, i).ok_or("EqualitySymbol equalTerm")?,
            neq: term_hook_sym(spec, "notEqualTerm", name_to_sym, i).ok_or("EqualitySymbol notEqualTerm")?,
        },
        "BranchSymbol" => {
            // term-hooks "1", "2", … are the test constants, in order.
            let mut tests = Vec::new();
            for k in 1.. {
                match term_hook_sym(spec, &k.to_string(), name_to_sym, i) {
                    Some(s) => tests.push(s),
                    None => break,
                }
            }
            SpecialOp::Branch { tests }
        }
        "ACU_NumberOpSymbol" => SpecialOp::AcuNumberOp {
            op: num_op(code.ok_or("ACU_NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "NumberOpSymbol" => SpecialOp::NumberOp {
            op: num_op(code.ok_or("NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
            bool_: bool_hooks(spec, name_to_sym, i),
        },
        "StringOpSymbol" => SpecialOp::StringOp {
            op: str_op(code.ok_or("StringOpSymbol code")?)?,
            str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i)
                .ok_or("StringOpSymbol stringSymbol")?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i).ok(),
            bool_: bool_hooks(spec, name_to_sym, i),
        },
        "FloatOpSymbol" => SpecialOp::FloatOp {
            op: flt_op(code.ok_or("FloatOpSymbol code")?, arity)?,
            float_sym: op_hook_sym(spec, "floatSymbol", name_to_sym, i)
                .ok_or("FloatOpSymbol floatSymbol")?,
            bool_: bool_hooks(spec, name_to_sym, i),
        },
        other => return Err(format!("unsupported special id-hook `{other}`")),
    };
    Ok(Some(op))
}

fn num_op(code: &str) -> R<NumOp> {
    Ok(match code {
        "+" => NumOp::Add,
        "*" => NumOp::Mul,
        "gcd" => NumOp::Gcd,
        "lcm" => NumOp::Lcm,
        "min" => NumOp::Min,
        "max" => NumOp::Max,
        "-" => NumOp::Sub,
        "quo" => NumOp::Quo,
        "rem" => NumOp::Rem,
        "^" => NumOp::Pow,
        "<" => NumOp::Lt,
        "<=" => NumOp::Le,
        ">" => NumOp::Gt,
        ">=" => NumOp::Ge,
        "divides" => NumOp::Divides,
        other => return Err(format!("unsupported number op `{other}`")),
    })
}

fn str_op(code: &str) -> R<StrOp> {
    Ok(match code {
        "+" => StrOp::Concat,
        "length" => StrOp::Length,
        "substr" => StrOp::Substr,
        "<" => StrOp::Lt,
        "<=" => StrOp::Le,
        ">" => StrOp::Gt,
        ">=" => StrOp::Ge,
        other => return Err(format!("unsupported string op `{other}`")),
    })
}

fn flt_op(code: &str, arity: usize) -> R<FltOp> {
    Ok(match (code, arity) {
        ("-", 1) => FltOp::Neg,
        ("abs", _) => FltOp::Abs,
        ("sqrt", _) => FltOp::Sqrt,
        ("+", _) => FltOp::Add,
        ("-", _) => FltOp::Sub,
        ("*", _) => FltOp::Mul,
        ("/", _) => FltOp::Div,
        ("<", _) => FltOp::Lt,
        ("<=", _) => FltOp::Le,
        (">", _) => FltOp::Gt,
        (">=", _) => FltOp::Ge,
        (other, _) => return Err(format!("unsupported float op `{other}`")),
    })
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::surface::parser::Parser;

    fn build(src: &str) -> BuiltModule {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse ok");
        build_module(&s.modules[0], &mut i).expect("build ok")
    }

    /// B4.2 done-when: the parsed signature is the same one the hand-built B3.4 test constructs — proven by
    /// reducing through the attached special ops (no equations needed; arithmetic is built-in).
    #[test]
    fn nat_signature_reduces_via_special_ops() {
        let src = "\
fmod NATB is
  sorts Truth Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  ops tt ff : -> Truth [ctor] .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  op _+_ : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (+) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _+_ : Nat Nat -> Nat [ditto] .
  op gcd : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (gcd) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op gcd : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
endfm
";
        let mut m = build(src);
        let (succ, zero) = (m.nat_succ.unwrap(), m.nat_zero.unwrap());
        let num = |m: &mut BuiltModule, n: u64| {
            let z = m.engine.make_const(zero);
            m.engine.make_iter(succ, n, z)
        };
        // 2 + 3 = 5 (ACU_NumberOp), NzNat, 1 rewrite.
        let plus = m.ops[&("_+_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let sum = m.engine.make_ac(plus, vec![a, b]);
        m.engine.reset_rewrites();
        let r = m.engine.reduce(sum);
        let five = num(&mut m, 5);
        assert!(m.engine.deep_equal(r, five), "2 + 3 = 5");
        assert_eq!(m.engine.sorts().name(m.engine.sort_of(r)), "NzNat");
        assert_eq!(m.engine.rewrites(), 1);

        // gcd(12, 18) = 6.
        let gcd = m.ops[&("gcd".to_string(), 2)];
        let (a, b) = (num(&mut m, 12), num(&mut m, 18));
        let g = m.engine.make_ac(gcd, vec![a, b]);
        let r = m.engine.reduce(g);
        let six = num(&mut m, 6);
        assert!(m.engine.deep_equal(r, six), "gcd(12, 18) = 6");

        // The `_<_` NumberOp produced a Truth result: 2 < 3 = tt.
        let lt = m.ops[&("_<_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let q = m.engine.make_free(lt, vec![a, b]);
        let r = m.engine.reduce(q);
        let tt = m.ops[&("tt".to_string(), 0)];
        let tt_node = m.engine.make_const(tt);
        assert!(m.engine.deep_equal(r, tt_node), "2 < 3 = tt");
    }
}
