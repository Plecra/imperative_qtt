use super::{InferState, InferError, Mult, Usage};
use crate::ast::TyRef;
use crate::HashMapExt;
// join across our subtyping lattice on contexts
pub trait Join {
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
