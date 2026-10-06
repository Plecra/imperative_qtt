use crate::ast::*;
use crate::HashMapExt;
pub fn ret(t: Target, v: TyRef, usage: Usage) -> Exits {
    Exits(HashMap::from([(t, (v, usage))]))
}
use Target as L;
// A bidi implementation of this algorithm should be feeding expected types for each exit
// down the tree: That looks very viable, but it makes this much worse as teaching material,
// because a lot of code noise shows up in the process.
pub fn infer(st: &mut InferState, unit: &TyRef, expr: &ExprNode) -> Exits {
    match expr {
        Expr::Var(n) => ret(L::Value, st.get_var(*n), st.use_var(*n)),
        Expr::Loop(body) => {
            // A loop expression captures `break` and `continue`, exiting to `value` with `break`'s signature,
            // and updating all the usages to happen after some unknown `n` iterations.
            // we also add the new style of divergence in case we keep `continue`ing

            // TODO(fix): extend check to check signatures of *all* exits, so it checks `continue` as well.
            let mut body_exits = check(st, unit, &body.0, &unit.0);
            let value = body_exits.take(L::Value).map(|u| u.1);
            let cont = body_exits.take(L::Continue).map(|u| u.1);
            let reentry_env = st.join(value, cont).map(Usage::many);

            let res = body_exits.take(L::Break);
            body_exits.0.set(L::Value, res);

            let first_iter = Usage::new();
            let reentry_usage = reentry_env.as_ref().unwrap_or(&first_iter);
            // All the remaining targets, including `Value` and possibly `Diverging`
            for (_, usage) in body_exits.0.values_mut() {
                usage.add(reentry_usage);
            }

            body_exits.modify(L::Diverging, |u| {
                st.join(u, reentry_env.map(|v| (unit.clone(), v)))
            });
            body_exits
        }
        Expr::Break(v) => {
            let mut exits = infer(st, unit, &v.0);
            let value = exits.take(L::Value);
            exits.modify(L::Break, |u| st.join(u, value));
            exits
        }
        Expr::Continue => ret(L::Continue, unit.clone(), Usage::new()),
        Expr::UnitValue => ret(L::Value, unit.clone(), Usage::new()),
        Expr::Ann(e, t) => check(st, unit, &e.0, &t.0),
        Expr::App(f, arg) => {
            let mut f_exits = infer(st, unit, &f.0);
            let mut arg_exits = infer(st, unit, &arg.0);
            let Some((f_ty, f_usage)) = f_exits.take(L::Value) else {
                return f_exits;
            };
            let arg_exit = arg_exits.take(L::Value);

            let retty = if let TyNode::Fun(n, a, r) = &*f_ty.0 {
                // The multiplicity `n` describes whether the parameter is actually relevant.
                // We dont need to consume the uses in the parameter if it's TyMult::Zero,
                // *however* that's only true for pure expressions. If the `value` exit is reached
                // without any side effects we can apply this reasoning, but otherwise we do need
                // to consume the usage like normal, it's just that the final value itself can be
                // discarded.
                //
                // In principle we could get more precise and track the usage that flowed into
                // side effects within each path. I think I'll just be using this relevance reasoning
                // on pure expressions though.
                _ = n;
                if let Some((ty, _)) = arg_exit.as_ref()
                    && a != ty
                {
                    st.errors.push(InferError::ArgTypeMismatch);
                }
                r
            } else {
                st.errors.push(InferError::NotAFunction);
                println!("not a func? {:?}", f_ty);
                unit
            };
            arg_exits
                .0
                .set(L::Value, arg_exit.map(|(_, u)| (retty.clone(), u)));
            arg_exits.0.iter_mut().for_each(|(_, u)| u.1.add(&f_usage));
            for (t, exit) in f_exits.0 {
                arg_exits.modify(t, |b| st.join(b, Some(exit)));
            }
            arg_exits
        }
        Expr::Lam(ty, e) => {
            let argt = ty.as_ref().unwrap_or_else(|| {
                st.errors.push(InferError::MissingLambdaArgumentType);
                unit
            });
            st.locals.push(argt.clone());
            let mut exits = infer(st, unit, &e.0);
            st.locals.pop();

            let value = exits.take(L::Value);
            let div = exits.take(L::Diverging);
            // lambdas have only one exit
            if !exits.0.is_empty() {
                st.errors.push(InferError::UnexpectedControlFlow);
            }
            // We need to accumulate the maximum usage for all possible paths
            let ret_ty = value.as_ref().map(|(ty, _)| ty).unwrap_or(unit).clone();
            let mut usage = value
                .map(|(_, u)| u)
                .join(div.map(|(_, u)| u), st)
                .unwrap_or(Usage::new());
            println!("{:?}", usage);
            let fnty = TyNode::Fun(
                match usage.0.remove(&(st.locals.len() as u32)) {
                    Mult::MAX_ONE | Mult::ZERO => todo!("argt must be drop"),
                    Mult::ONE => TyMult::One,
                    Mult::MANY => todo!("argt must be copy"),
                },
                argt.clone(),
                // TODO: !-type is a more appropriate fallback than `st.unit.clone()` here
                ret_ty,
            ).rc();
            // Careful with the semantics of usage here: A binding being used 'many' times
            // basically just means it needs a copy impl. In this case, that'll be applied
            // within the body.
            // We might need to make a distinction here later.
            Exits(HashMap::from([(Target::Value, (fnty, usage))]))
        }
        Expr::Let(ty, value, body) => {
            let mut value_exits = if let Some(t) = ty {
                check(st, unit, &value.0, &t.0)
            } else {
                infer(st, unit, &value.0)
            };
            let (vty, val_usage) = value_exits
                .take(Target::Value)
                .unwrap_or((unit.clone(), Usage::new()));

            st.locals.push(vty);
            let mut exits = infer(st, unit, &body.0);
            st.locals.pop();

            let n = st.locals.len() as u32;
            let mult = exits
                .0
                .values_mut()
                .map(|(_, u)| u.0.remove(&n))
                .reduce(|a, x| a.join(x, st))
                .unwrap_or(Mult::ZERO);
            match mult {
                // The Drop+Copy insertions can also mean that we're using extra lifetimes.
                Mult::ZERO | Mult::MAX_ONE => todo!("vty must be drop"),
                Mult::ONE => (),
                Mult::MANY => todo!("vty must be copy"),
            }

            exits.0.iter_mut().for_each(|(_, u)| u.1.add(&val_usage));
            for (t, exit) in value_exits.0 {
                exits.modify(t, |b| st.join(b, Some(exit)));
            }
            exits
        }
        Expr::LetPair(ty, value, body) => {
            let mut value_exits = if let Some(t) = ty {
                check(st, unit, &value.0, &t.0)
            } else {
                infer(st, unit, &value.0)
            };
            let (fty, sty, val_usage) = value_exits
                .take(Target::Value)
                .map(|(t, u)| match &*t.0 {
                    Ty::Pair(l, r) => (l.clone(), r.clone(), u),
                    _ => {
                        st.errors.push(InferError::TypeMismatch);
                        (unit.clone(), unit.clone(), u)
                    },
                })
                .unwrap_or_else(|| (unit.clone(), unit.clone(), Usage::new()));

            st.locals.push(fty);
            st.locals.push(sty);
            let mut exits = infer(st, unit, &body.0);
            st.locals.pop();
            st.locals.pop();

            let n = st.locals.len() as u32;
            let (mult0, mult1) = exits
                .0
                .values_mut()
                .map(|(_, usage)| (usage.0.remove(&n), usage.0.remove(&(n + 1))))
                .reduce(|(a0, a1), (x, y)| (a0.join(x, st), a1.join(y, st)))
                .unwrap_or((Mult::ZERO, Mult::ZERO));
            match mult0 {
                // The Drop+Copy insertions can also mean that we're using extra lifetimes.
                Mult::ZERO | Mult::MAX_ONE => todo!("vty must be drop"),
                Mult::ONE => (),
                Mult::MANY => todo!("vty must be copy"),
            }
            match mult1 {
                // The Drop+Copy insertions can also mean that we're using extra lifetimes.
                Mult::ZERO | Mult::MAX_ONE => todo!("vty must be drop"),
                Mult::ONE => (),
                Mult::MANY => todo!("vty must be copy"),
            }

            exits.0.iter_mut().for_each(|(_, u)| u.1.add(&val_usage));
            for (t, exit) in value_exits.0 {
                exits.modify(t, |b| st.join(b, Some(exit)));
            }
            exits
        }
        Expr::Case(scrutinee, l, r) => {
            let mut scrutinee_exits = infer(st, unit, &scrutinee.0);
            let (lty, rty, usage) = match scrutinee_exits.take(Target::Value) {
                Some((ty, usage)) => match &*ty.0 {
                    Ty::Sum(l, r) => (l.clone(), r.clone(), usage),
                    _ => {
                        st.errors.push(InferError::TypeMismatch);
                        (unit.clone(), unit.clone(), usage)
                    },
                },
                None => (unit.clone(), unit.clone(), Usage::new()),
            };

            st.locals.push(lty);
            let mut l_exits = infer(st, unit, &l.0);
            st.locals.pop();
            
            let n = st.locals.len() as u32;
            let mult = l_exits
                .0
                .values_mut()
                .map(|(_, u)| u.0.remove(&n))
                .reduce(|a, x| a.join(x, st))
                .unwrap_or(Mult::ZERO);
            match mult {
                // The Drop+Copy insertions can also mean that we're using extra lifetimes.
                Mult::ZERO | Mult::MAX_ONE => todo!("vty must be drop"),
                Mult::ONE => (),
                Mult::MANY => todo!("vty must be copy"),
            }
            st.locals.push(rty);
            let mut r_exits = infer(st, unit, &r.0);
            st.locals.pop();
            
            let n = st.locals.len() as u32;
            let mult = r_exits
                .0
                .values_mut()
                .map(|(_, u)| u.0.remove(&n))
                .reduce(|a, x| a.join(x, st))
                .unwrap_or(Mult::ZERO);
            match mult {
                // The Drop+Copy insertions can also mean that we're using extra lifetimes.
                Mult::ZERO | Mult::MAX_ONE => todo!("vty must be drop"),
                Mult::ONE => (),
                Mult::MANY => todo!("vty must be copy"),
            }

            l_exits.0.iter_mut().for_each(|(_, u)| u.1.add(&usage));
            r_exits.0.iter_mut().for_each(|(_, u)| u.1.add(&usage));

            let mut exits = l_exits;
            for (t, exit) in r_exits.0 {
                exits.modify(t, |b| st.join(b, Some(exit)));
            }
            for (t, exit) in scrutinee_exits.0 {
                exits.modify(t, |b| st.join(b, Some(exit)));
            }
            exits
        }
    }
}
fn check(st: &mut InferState, unit: &TyRef, expr: &ExprNode, t: &TyNode) -> Exits {
    let exits = infer(st, unit, expr);
    if let Some((inferred_ty, _)) = exits.get(Target::Value)
        // TODO: Can apply subtyping here with eg weakening multiplicities
        && &*inferred_ty.0 != t
    {
        st.errors.push(InferError::TypeMismatch);
    }
    exits
}

#[derive(PartialEq, Eq, Hash, Debug, Clone)]
pub enum Target {
    Value,
    Diverging,
    Continue,
    Break,
}
use std::collections::HashMap;
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mult {
    One,
    MaxOne,
    Many,
}
impl Mult {
    const ZERO: Option<Mult> = None;
    const ONE: Option<Mult> = Some(Mult::One);
    const MAX_ONE: Option<Mult> = Some(Mult::MaxOne);
    const MANY: Option<Mult> = Some(Mult::Many);
}
// DBLs
#[derive(Debug, Clone)]
pub struct Usage(pub HashMap<u32, Mult>);
#[derive(Debug)]
pub struct Exits(pub HashMap<Target, (TyRef, Usage)>);
// impl
impl Exits {
    fn get(&self, target: Target) -> Option<&(TyRef, Usage)> {
        self.0.get(&target)
    }
    fn take(&mut self, target: Target) -> Option<(TyRef, Usage)> {
        self.0.remove(&target)
    }
    fn modify(
        &mut self,
        target: Target,
        f: impl FnOnce(Option<(TyRef, Usage)>) -> Option<(TyRef, Usage)>,
    ) {
        let v = f(self.take(target.clone()));
        self.0.set(target, v);
    }
}

#[derive(Debug)]
pub enum InferError {
    MissingLambdaArgumentType,
    UnexpectedControlFlow,
    TypeMismatch,
    ArgTypeMismatch,
    NotAFunction,
}
impl Usage {
    fn new() -> Self {
        Usage(HashMap::new())
    }
    fn many(mut self) -> Self {
        for (_, v) in self.0.iter_mut() {
            *v = Mult::Many;
        }
        self
    }
    // forall e1 e2. usage(e1; e2) = usage(e1) + usage(e2)
    // this is symmetric at the moment
    fn add(&mut self, other: &Usage) {
        for (k, v) in &other.0 {
            // iow: self.set(k, sequence(self.get(k), Some(*v)))
            self.0
                .entry(*k)
                .and_modify(|e| *e = Mult::Many)
                .or_insert(*v);
        }
    }
}
pub(crate) struct InferState {
    pub(crate) locals: Vec<TyRef>,
    pub(crate) errors: Vec<InferError>,
}
impl InferState {
    fn use_var(&self, n: u32) -> Usage {
        let mut usage = Usage::new();
        usage.0.insert((self.locals.len() as u32 - 1) - n, Mult::One);
        usage
    }
    fn get_var(&self, n: u32) -> TyRef {
        self.locals[((self.locals.len() as u32 - 1) - n) as usize].clone()
    }
    fn join<T: Join>(&mut self, a: T, b: T) -> T {
        a.join(b, self)
    }
}
// join across our subtyping lattice on contexts
trait Join {
    fn join(mut self, other: Self, st: &mut InferState) -> Self
    where
        Self: Sized,
    {
        self.join_assign(&other, st);
        self
    }
    fn join_assign(&mut self, other: &Self, st: &mut InferState);
}
impl Join for Option<Mult> {
    fn join_assign(&mut self, other: &Self, _: &mut InferState) {
        // 0 <: MaxOne
        // 1 <: MaxOne
        // MaxOne <: Many
        match (*self, *other) {
            (Mult::ZERO, Mult::ZERO) | (Mult::ONE, Mult::ONE) | (Mult::MAX_ONE, Mult::MAX_ONE) => {}
            (Mult::MANY, _) | (_, Mult::MANY) => *self = Mult::MANY,
            _ => *self = Mult::MAX_ONE,
        }
    }
}
impl<A: Join, B: Join> Join for (A, B) {
    fn join_assign(&mut self, other: &Self, st: &mut InferState) {
        self.0.join_assign(&other.0, st);
        self.1.join_assign(&other.1, st);
    }
}
impl Join for Usage {
    fn join_assign(&mut self, other: &Self, st: &mut InferState) {
        // join(m1, m2) = \ident -> join(m1 ident, m2 ident)
        for (k, v) in &other.0 {
            self.0.set(*k, self.0.get(k).copied().join(Some(*v), st));
        }
        for (k, v) in &mut self.0 {
            *v = Some(*v).join(other.0.get(k).copied(), st).unwrap();
        }
    }
}
impl Join for TyRef {
    fn join_assign(&mut self, other: &Self, st: &mut InferState) {
        if self != other {
            st.errors.push(InferError::TypeMismatch);
        }
    }
}
impl<T: Join + Clone> Join for Option<T> {
    fn join_assign(&mut self, other: &Self, st: &mut InferState) {
        match (&mut *self, other) {
            (Some(a), Some(b)) => a.join_assign(b, st),
            (Some(_), None) => (),
            (None, Some(v)) => *self = Some(v.clone()),
            (None, None) => (),
        }
    }
    fn join(self, other: Self, st: &mut InferState) -> Self {
        match (self, other) {
            (Some(a), Some(b)) => Some(a.join(b, st)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }
}
