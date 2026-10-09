pub type Desc {
  Desc(clone: Bool, drop: Bool)
}

pub const linear: Desc = Desc(False, False)

pub const affine: Desc = Desc(False, True)

pub const relevant: Desc = Desc(True, False)

pub const normal: Desc = Desc(True, True)

pub fn and_desc(a: Desc, b: Desc) -> Desc {
  Desc(a.clone && b.clone, a.drop && b.drop)
}

pub fn desc(t: Type) -> Desc {
  case t {
    Unit -> normal
    Pair(a, b) -> and_desc(desc(a), desc(b))
    Sum(a, b) -> and_desc(desc(a), desc(b))
    Never -> normal
    Fun(n, _, _) -> n
    Buffer -> affine
    OutPointer -> linear
  }
}

pub type Type {
  //   Int
  Unit
  Fun(Desc, Type, Type)
  Pair(Type, Type)
  Sum(Type, Type)
  Never

  Buffer
  OutPointer
}

pub type Pat {
  Bind
  Cons
  Left
  Right
}

pub const break_jump_offset: Int = 0

pub const continue_jump_offset: Int = 1

pub type JumpName =
  Int

// We can consider adding a 'tap' multiplicity: This type-preserving updates a binder
// and is fundamentally pretty mutable. It's "between" 1 and 0, and makes ordering important.
// (Tap, 1) is ~1, (1, Tap) is Omega
pub type Expr {
  App(Expr, Expr)
  Lam(Type, Expr)
  Var(Int)
  Case(Expr, List(#(Pat, Expr)))

  Loop(Expr, Expr)
  Jump(JumpName, Expr)
}
