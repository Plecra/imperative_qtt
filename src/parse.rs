use crate::ast::{Expr, ExprNode, ExprRef, Ty, TyMult, TyNode, TyRef};
pub enum Error {
    ExpectedIdentifier,
    ExpectedSymbol(&'static [u8]),
}
fn ws(input: &mut &[u8]) {
    while let Some(rem) = input.strip_prefix(b" ") {
        *input = rem;
    }
}
fn try_eat(input: &mut &[u8], sym: &[u8]) -> bool {
    if let Some(rem) = input.strip_prefix(sym) {
        *input = rem;
        ws(input);
        true
    } else {
        false
    }
}
fn eat(input: &mut &[u8], sym: &'static [u8], errors: &mut Vec<Error>) {
    if !try_eat(input, sym) {
        errors.push(Error::ExpectedSymbol(sym));
    }
}
fn try_ident<'a>(input: &mut &'a [u8]) -> Option<&'a [u8]> {
    let mut i = 0;
    while i < input.len() && (input[i] as char).is_alphanumeric() {
        i += 1;
    }
    let ident = &input[..i];
    if ident.is_empty() {
        None
    } else {
        *input = &input[i..];
        ws(input);
        Some(ident)
    }
}
fn ident<'a>(input: &mut &'a [u8], errors: &mut Vec<Error>) -> &'a [u8] {
    match try_ident(input) {
        Some(ident) => ident,
        None => {
            errors.push(Error::ExpectedIdentifier);
            &[]
        }
    }
}
use std::collections::HashMap;
use crate::HashMapExt;
pub fn parse_ty(input: &mut &[u8], errors: &mut Vec<Error>) -> TyNode {
    let mut bad = false;
    let mut atom = loop {
        break if try_eat(input, b"(") {
            if try_eat(input, b")") {
                Ty::Unit
            } else {
                let ty = parse_ty(input, errors);
                eat(input, b")", errors);
                ty
            }
        } else if try_eat(input, b"Sum") {
            let left = parse_ty(input, errors);
            eat(input, b",", errors);
            let right = parse_ty(input, errors);
            eat(input, b")", errors);
            Ty::Sum(left.rc(), right.rc())
        } else if try_eat(input, b"Pair") {
            let left = parse_ty(input, errors);
            eat(input, b",", errors);
            let right = parse_ty(input, errors);
            eat(input, b")", errors);
            Ty::Pair(left.rc(), right.rc())
        } else {
            if !std::mem::replace(&mut bad, true) {
                errors.push(Error::ExpectedSymbol(b"("));
            }
            continue;
        }
    };
    while try_eat(input, b"->") {
        let ret = parse_ty(input, errors);
        atom = Ty::Fun(TyMult::One, atom.rc(), ret.rc());
    }
    atom
}
// prec 0 allows ;, 1 doesnt.
pub fn parse_expr<'a>(
    input: &mut &'a [u8],
    context: &mut HashMap<&'a [u8], u32>,
    skips: &mut u32,
    unit_ty: &TyRef,
    errors: &mut Vec<Error>,
    prec: u32,
) -> ExprNode {
    let mut bad = false;
    let mut atom = loop {
        break if try_eat(input, b"let") {
            let pat = if try_eat(input, b"[") {
                let name1 = ident(input, errors);
                eat(input, b",", errors);
                let name2 = ident(input, errors);
                eat(input, b"]", errors);
                Ok((name1, name2))
            } else {
                Err(ident(input, errors))
            };
            let ty = try_eat(input, b":").then(|| parse_ty(input, errors).rc());
            eat(input, b"=", errors);
            let value = parse_expr(input, context, skips, unit_ty, errors, 1);
            eat(input, b";", errors);
            match pat {
                Ok((name1, name2)) => {
                    let old1 = context.insert(name1, *skips + context.len() as u32);
                    let old2 = context.insert(name2, *skips + context.len() as u32);
                    let body = parse_expr(input, context, skips, unit_ty, errors, 0);
                    context.set(name1, old1);
                    context.set(name2, old2);
                    Expr::LetPair(Some(unit_ty.clone()), value.rc(), body.rc())
                }
                Err(name) => {
                    let old = context.insert(name, *skips + context.len() as u32);
                    let body = parse_expr(input, context, skips, unit_ty, errors, 0);
                    context.set(name, old);
                    Expr::Let(ty, value.rc(), body.rc())
                }
            }
        }  else if try_eat(input, b"loop") {
            let body = parse_expr(input, context, skips, unit_ty, errors, 1);
            Expr::Loop(body.rc())
        } else if try_eat(input, b"break") {
            let value = parse_expr(input, context, skips, unit_ty, errors, 1);
            Expr::Break(value.rc())
        } else if try_eat(input, b"continue") {
            Expr::Continue
        } else if try_eat(input, b"case") {
            let scrutinee = parse_expr(input, context, skips, unit_ty, errors, 1);
            eat(input, b"of", errors);
            let ident1 = ident(input, errors);
            eat(input, b"=>", errors);
            let old = context.insert(ident1, *skips + context.len() as u32);
            let body1 = parse_expr(input, context, skips, unit_ty, errors, 1);
            context.set(ident1, old);
            eat(input, b"|", errors);
            let ident2 = ident(input, errors);
            eat(input, b"=>", errors);
            let old = context.insert(ident2, *skips + context.len() as u32);
            let body2 = parse_expr(input, context, skips, unit_ty, errors, 1);
            context.set(ident2, old);
            Expr::Case(scrutinee.rc(), body1.rc(), body2.rc())
        } else if try_eat(input, b"fun") {
            let ident = ident(input, errors);
            let ty = try_eat(input, b":").then(|| parse_ty(input, errors).rc());
            eat(input, b"=>", errors);
            println!("parse fn {:?}", input);
            let old = context.insert(ident, *skips + context.len() as u32);
            let body = parse_expr(input, context, skips, unit_ty, errors, 1);
            context.set(ident, old);
            Expr::Lam(ty, body.rc())
        } else if try_eat(input, b"(") {
            if try_eat(input, b")") {
                Expr::UnitValue
            } else {
                let expr = parse_expr(input, context, skips, unit_ty, errors, 0);
                eat(input, b")", errors);
                expr
            }
        }else if let Some(v) = try_ident(input) {
            println!("{context:?}");
            Expr::Var((*skips + context.len() as u32 - 1) - *context.get(v).expect("Variable not in scope"))
        } else {
            if !std::mem::replace(&mut bad, true) {
                errors.push(Error::ExpectedSymbol(b"let"));
            }
            continue;
        }
    };
    loop {
        if prec < 2 && try_eat(input, b":") {
            let ty = parse_ty(input, errors).rc();
            atom = Expr::Ann(atom.rc(), ty);
        } else if prec < 1 && try_eat(input, b";") {
            *skips += 1;
            let rhs = parse_expr(input, context, skips, unit_ty, errors, 0);
            *skips -= 1;
            atom = Expr::Let(Some(unit_ty.clone()), atom.rc(), rhs.rc());
        } else if input.first().is_some_and(|v| *v == b'(' || v.is_ascii_alphanumeric()) {
            let rhs = parse_expr(input, context, skips, unit_ty, errors, 2);
            atom = Expr::App(atom.rc(), rhs.rc());
        } else {
            break;
        }
    }
    atom
}
