// import gleam/bool
import ast.{
  type Expr, type JumpName, type Pat, type Type, Bind, Break, Cons, Continue,
  Fun, Left, Never, Pair, Right, Sum, Unit,
}
import dictex.{type Maybe}
import gleam/bool
import gleam/dict.{type Dict, from_list as entries}
import gleam/list
import gleam/option.{None, Some}
import gleam/result.{try} as res

pub type Target {
  Value
  Named(JumpName)
  Diverge
}

type Context =
  Dict(Int, Type)

fn with_var(context: Context, ty: Type) -> Context {
  dict.insert(context, dict.size(context), ty)
}

fn var(cx: Context, i: Int) -> Result(#(Int, Type), Issue) {
  let level = { dict.size(cx) - 1 } - i
  dict.get(cx, level)
  |> res.map(fn(ty) { #(level, ty) })
  |> res.replace_error(#(UndefinedVariable, Here))
}

pub type Mult {
  One
  MaxOne
  Many
}

pub type Error {
  PatternMismatch
  InfersWrong(infers_to: Type, context_demands: Type, e: Expr)
  UndefinedVariable
  IncompatibleExits(a: Exit, b: Exit)
  NeedsClone(ty: Type)
  NeedsDrop(ty: Type)
  LamBodyJump(exits: Exits)
  AppNotFun(infers_to: Type)
}

pub type Issue =
  #(Error, Loc)

fn fail(e: Error) -> Result(a, Issue) {
  Error(#(e, Here))
}

type Usage =
  Dict(Int, Mult)

type Exit =
  #(Type, Usage)

type Exits =
  Dict(Target, Exit)

fn join_mult(a: Maybe(Mult), b: Maybe(Mult)) -> Maybe(Mult) {
  case a, b {
    _, _ if a == b -> a
    Ok(Many), _ | _, Ok(Many) -> Ok(Many)
    _, _ -> Ok(MaxOne)
  }
}

fn join_usage(a: Usage, b: Usage) -> Usage {
  dictex.join(a, b, join_mult)
}

fn join_exit(a: Exit, b: Exit) -> Result(Exit, Issue) {
  case a.0 == b.0 {
    True -> Ok(#(a.0, join_usage(a.1, b.1)))
    False -> {
      fail(IncompatibleExits(a, b))
    }
  }
}

fn join_opt_usage(a: Maybe(Usage), b: Maybe(Usage)) -> Maybe(Usage) {
  case a, b {
    Ok(a), Ok(b) -> Ok(join_usage(a, b))
    Ok(a), _ -> Ok(a)
    _, v -> v
  }
}

fn join_opt_exit(a: Maybe(Exit), b: Maybe(Exit)) -> Result(Maybe(Exit), Issue) {
  case a, b {
    Ok(a), Ok(b) -> join_exit(a, b) |> res.map(fn(e) { Ok(e) })
    Error(Nil), _ -> Ok(b)
    Ok(a), _ -> Ok(Ok(a))
  }
}

fn join_exits(a: Exits, b: Exits) -> Result(Exits, Issue) {
  dictex.try_combine(a, b, join_exit)
}

// What is the usage of the context if an expression is repeated an unbounded number of times?
fn many(usage: Usage) -> Usage {
  dict.map_values(usage, fn(_, _) { Many })
}

fn seq(a: Usage, b: Usage) -> Usage {
  dict.combine(a, b, fn(_, _) { Many })
}

fn uses_of_bind(
  cx: Context,
  ty: Type,
  f: fn(Context) -> Result(Exits, a),
) -> Result(#(Exits, Maybe(Mult)), a) {
  use v <- try(f(cx |> with_var(ty)))
  Ok(#(
    dict.map_values(v, fn(_, s) { #(s.0, dict.delete(s.1, dict.size(cx))) }),
    dict.values(v)
      |> list.map(fn(s) { dict.get(s.1, dict.size(cx)) })
      |> list.reduce(join_mult)
      |> res.unwrap(dictex.missing),
  ))
}

fn with_bind(
  cx: Context,
  ty: Type,
  f: fn(Context) -> Result(Exits, Issue),
) -> Result(Exits, Issue) {
  use #(exits, uses) <- try(uses_of_bind(cx, ty, f))
  echo exits
  let needs = case uses {
    Error(Nil) | Ok(MaxOne) -> ast.affine
    Ok(One) -> ast.linear
    Ok(Many) -> ast.normal
  }
  let supports = ast.desc(ty)
  case #() {
    _ if needs.clone && !supports.clone -> fail(NeedsClone(ty))
    _ if needs.drop && !supports.drop -> fail(NeedsDrop(ty))
    _ -> Ok(exits)
  }
}

fn exit_usage(exit: Maybe(Exit)) -> Maybe(Usage) {
  exit |> res.map(fn(x) { x.1 })
}

fn after(step: Exits, exit: Usage, after: Exits) -> Result(Exits, Issue) {
  dict.map_values(step, fn(_, s) { #(s.0, seq(exit, s.1)) })
  |> join_exits(after)
}

fn check(cx: Context, e: Expr, at: Target, ret: Type) -> Result(Exits, Issue) {
  use exits <- try(infer(cx, e))
  use <- option.lazy_unwrap(case dict.get(exits, at) {
    Ok(#(found, _)) if found != ret -> Some(fail(InfersWrong(found, ret, e)))
    _ -> None
  })
  Ok(exits)
}

// A lightweight method for keeping enough error location information in the AST.
// I'd recommend using expression identities instead, but that would make the gleam
// code much noisier.
pub type Loc {
  Here
  Child(Int, Loc)
}

fn at(r: Result(a, Issue), i: Int) -> Result(a, Issue) {
  r |> res.map_error(fn(e) { #(e.0, Child(i, e.1)) })
}

pub fn infer(cx: Context, e: Expr) -> Result(Exits, Issue) {
  case e {
    ast.Var(i) -> {
      use #(level, ty) <- try(var(cx, i))
      Ok(entries([#(Value, #(ty, entries([#(level, One)])))]))
    }
    ast.Jump(name, e) -> {
      use exits <- try(infer(cx, e) |> at(0))
      let #(a, b) = #(exits |> dict.get(Value), exits |> dict.get(Named(name)))
      use paths <- try(join_opt_exit(a, b))
      Ok(exits |> dict.delete(Value) |> dictex.set(Named(name), paths))
    }
    ast.Loop(init, body) -> {
      use init_exits <- try(infer(cx, init) |> at(0))
      let init = dict.get(init_exits, Value)
      let #(ty, init_u) = init |> res.unwrap(#(Never, entries([])))

      use exits <- try(with_bind(cx, ty, fn(cx) { infer(cx, body) |> at(1) }))
      use acc <- try(join_opt_exit(
        dict.get(exits, Value),
        dict.get(exits, Named(Continue)),
      ))
      let reentry_env = acc |> res.map(fn(x) { #(x.0, seq(init_u, many(x.1))) })
      use entry_env <- try(join_opt_exit(init, reentry_env))
      // And the environment on each loop iteration is a result of those iterations (or only the first loop)
      let entry_u = entry_env |> exit_usage |> res.unwrap(entries([]))

      let exits =
        exits
        |> dict.delete(Named(Continue))
        |> dict.delete(Named(Break))
        |> dictex.set(Value, dict.get(exits, Named(Break)))
        // All the exits of the body come after an entry
        |> dict.map_values(fn(_, s) { #(s.0, seq(entry_u, s.1)) })

      let div_inner = dict.get(exits, Diverge) |> exit_usage
      // We can diverge after a sequence of loop iterations
      let div = join_opt_usage(div_inner, reentry_env |> exit_usage)
      Ok(dictex.set(exits, Diverge, div |> res.map(fn(x) { #(Never, x) })))
    }
    ast.Lam(ty, body) -> {
      use exits <- try(with_bind(cx, ty, fn(cx) { infer(cx, body) |> at(0) }))
      let value = dict.get(exits, Value)
      let exitn = dict.size(exits |> dict.delete(Value) |> dict.delete(Diverge))
      use <- bool.guard(when: exitn != 0, return: fail(LamBodyJump(exits)))

      // Find the captures as the variables in use on any path
      let anypath =
        dict.values(exits)
        |> list.map(fn(v) { v.1 })
        |> list.reduce(join_usage)
        |> res.unwrap(entries([]))

      // Find the description of the captures
      let cx_desc =
        dict.keys(anypath)
        |> list.fold(ast.normal, fn(acc, x) {
          ast.and_desc(acc, ast.desc(dictex.index(cx, x)))
        })
      let body_ty = value |> res.map(fn(x) { x.0 }) |> res.unwrap(Never)
      Ok(entries([#(Value, #(Fun(cx_desc, ty, body_ty), anypath))]))
    }
    ast.App(a, b) -> {
      use a_exits <- try(infer(cx, a) |> at(0))
      use #(arg, ret, usage) <- try(case dict.get(a_exits, Value) {
        Ok(#(Fun(_, arg, ret), usage)) -> Ok(#(arg, ret, Some(usage)))
        Ok(#(t, _)) -> fail(AppNotFun(t))
        Error(_) -> Ok(#(Unit, Never, None))
      })
      use b_exits <- try(check(cx, b, Value, arg) |> at(1))
      case usage {
        None -> Ok(a_exits)
        Some(rets) -> {
          let val = b_exits |> dict.get(Value) |> res.map(fn(x) { #(ret, x.1) })
          dictex.set(b_exits, Value, val)
          |> after(rets, dict.delete(a_exits, Value))
        }
      }
    }
    ast.Case(scrutinee, cases) -> {
      use exits <- try(infer(cx, scrutinee) |> at(0))
      let #(ty, usage) =
        dict.get(exits, Value) |> res.unwrap(#(Never, entries([])))
      use case_usage <- try(
        list.index_map(cases, fn(c, i) { #(c, i) })
        |> list.try_fold(entries([]), fn(exits, c) {
          let #(#(pat, body), i) = c
          let f = fn(cx) { infer(cx, body) |> at(i + 1) }
          use case_exits <- try(case pat, ty {
            Bind, _ -> with_bind(cx, ty, f)
            Left, Sum(left, _) -> with_bind(cx, left, f)
            Right, Sum(_, right) -> with_bind(cx, right, f)
            Cons, Pair(a, b) -> with_bind(cx, a, fn(cx) { with_bind(cx, b, f) })
            _, _ -> fail(PatternMismatch)
          })
          join_exits(case_exits, exits)
        }),
      )
      // We could make this more precise by sequencing *before* joining, inside
      // the fold. It's unclear whether that enables anything important - those
      // sequence calls dont have to deal with a lossy subtyping relation though.
      let res_usage = after(case_usage, usage, dict.delete(exits, Value))
      case dict.has_key(exits, Value) {
        True -> res_usage
        False -> Ok(exits)
      }
    }
  }
}
