/// Function types dont support the 'many' usage: copyability/contraction is a
/// property of types, not decided per call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyMult {
    Zero,
    One,
}
// /// Effect tracking is how we implement lifetimes: Functions have "read and write" effects that the type system has
// /// sophisticated tracking for.
// // This is part of the implementation of lifetimes
// struct EffSig {
//     // Tracks the `Zero` binders that we've late-bound to be 'used': This is a primitive notion that implements
//     // permissions, and means that the code observes its liveness, and updates it in a frame-preserving manner.
//     // (Any frame updates in this calculus are 'erased', we're not actually implementing them. I understand that this
//     // interpretation would be relevant when extending this technique to capture more of separation logic though.)
//     uses: Vec<u32>,
//     // Liveness is a use *and* a requirement that all dependencies of the type are live. This is necessary
//     // in judgements so that we can generalize permission types and still discuss the full transitive requirement
//     // that their parents are live.
//     live: Vec<u32>,
// }
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty<TyRef> {
    Fun(TyMult, TyRef, TyRef),
    // Suspended(EffSig, TyRef),

    Unit,
    Pair(TyRef, TyRef),
    Sum(TyRef, TyRef),
}
// DBI'd expressions.
#[derive(Debug, Clone)]
pub enum Expr<ERef, TyRef> {
    Var(u32),
    Let(Option<TyRef>, ERef, ERef),
    Ann(ERef, TyRef),
    
    // datatypes
    LetPair(Option<TyRef>, ERef, ERef),
    Case(ERef, ERef, ERef),
    UnitValue,
    
    // functions
    Lam(Option<TyRef>, ERef),
    App(ERef, ERef),
    // Suspend(ERef),
    
    // control flow
    Loop(ERef),
    Break(ERef),
    Continue,
}
pub use std::rc::Rc;
#[derive(Debug, Clone)]
pub struct ExprRef<TyRef>(pub Rc<Expr<ExprRef<TyRef>, TyRef>>);
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TyRef(pub Rc<Ty<TyRef>>);
impl TyNode {
    pub fn rc(self) -> TyRef {
        TyRef(Rc::new(self))
    }
}
pub type ExprNode = Expr<ExprRef<TyRef>, TyRef>;
pub type TyNode = Ty<TyRef>;
impl ExprNode {
    pub fn rc(self) -> ExprRef<TyRef> {
        ExprRef(Rc::new(self))
    }
}