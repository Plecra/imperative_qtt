import gleam/dict.{type Dict}
import gleam/result

pub type Maybe(a) =
  Result(a, Nil)

pub fn set(dict: Dict(a, b), k: a, v: Maybe(b)) -> Dict(a, b) {
  case v {
    Ok(v) -> dict.insert(dict, k, v)
    Error(Nil) -> dict.delete(dict, k)
  }
}

pub const missing: Maybe(a) = Error(Nil)

pub fn index(a: Dict(a, b), k: a) -> b {
  case dict.get(a, k) {
    Ok(v) -> v
    Error(Nil) -> panic
  }
}

fn try_combine_inner(
  a: List(#(a, b)),
  b: Dict(a, b),
  fun: fn(b, b) -> Result(b, e),
) -> Result(Dict(a, b), e) {
  case a {
    [] -> Ok(b)
    [#(k, av), ..xs] -> {
      case dict.get(b, k) {
        Ok(bv) -> {
          use v2 <- result.try(fun(av, bv))
          try_combine_inner(xs, dict.insert(b, k, v2), fun)
        }
        Error(Nil) -> try_combine_inner(xs, dict.insert(b, k, av), fun)
      }
    }
  }
}

pub fn try_combine(
  a: Dict(a, b),
  b: Dict(a, b),
  fun: fn(b, b) -> Result(b, e),
) -> Result(Dict(a, b), e) {
  case dict.size(a) >= dict.size(b) {
    True -> try_combine_inner(dict.to_list(b), a, fn(x, y) { fun(y, x) })
    False -> try_combine_inner(dict.to_list(a), b, fun)
  }
}

fn join_inner(
  a: Dict(a, b),
  b: Dict(a, c),
  fun: fn(Maybe(b), Maybe(c)) -> Maybe(d),
) -> Dict(a, d) {
  let d = dict.new()
  let d = dict.fold(a, d, fn(d, k, v) { set(d, k, fun(Ok(v), dict.get(b, k))) })
  dict.fold(b, d, fn(d, k, v) {
    case dict.has_key(a, k) {
      True -> d
      False -> set(d, k, fun(missing, Ok(v)))
    }
  })
}

pub fn join(
  a: Dict(a, b),
  b: Dict(a, c),
  fun: fn(Maybe(b), Maybe(c)) -> Maybe(d),
) -> Dict(a, d) {
  case dict.size(a) >= dict.size(b) {
    True -> join_inner(a, b, fun)
    False -> join_inner(b, a, fn(x, y) { fun(y, x) })
  }
}
