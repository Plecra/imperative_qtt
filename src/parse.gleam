import ast.{type Expr}
import dictex
import gleam/bit_array.{bit_size, slice}
import gleam/bool
import gleam/dict
import gleam/option.{type Option, None, Some}
import gleam/result.{try}

pub type Error {
  Expected(token: BitArray, at: BitArray)
  ExpectedIdent(at: BitArray)
  ExpectedType(at: BitArray)
  ExpectedStructure(at: BitArray)
  ExpectedEof(at: BitArray)
  UndefinedVariable(name: BitArray, at: BitArray)
}

type Parser(a) =
  fn(BitArray) -> Result(#(a, BitArray), Error)

fn strip_prefix(prefix: BitArray, input: BitArray) -> Result(BitArray, Nil) {
  case bit_array.starts_with(input, prefix) {
    True -> {
      slice(
        input,
        bit_array.byte_size(prefix),
        bit_array.byte_size(input) - bit_array.byte_size(prefix),
      )
    }
    False -> Error(Nil)
  }
}

fn skip_line(input: BitArray) -> BitArray {
  case input {
    <<"\n":utf8, rest:bytes>> -> rest
    <<_:size(8), rest:bytes>> -> skip_line(rest)
    _ -> input
  }
}

fn trim_start(input: BitArray) -> BitArray {
  case input {
    <<" ":utf8, rest:bytes>>
    | <<"\r":utf8, rest:bytes>>
    | <<"\n":utf8, rest:bytes>> -> trim_start(rest)
    <<"//":utf8, rest:bytes>> -> trim_start(skip_line(rest))
    _ -> input
  }
}

fn eat(token: BitArray) -> Parser(#()) {
  fn(x) {
    case strip_prefix(token, x) {
      Ok(v) -> Ok(#(#(), trim_start(v)))
      Error(Nil) -> Error(Expected(token, x))
    }
  }
}

fn alpha(c: Int) -> Bool {
  case c {
    x if { x >= 65 && x <= 90 } || { x >= 97 && x <= 122 } -> True
    _ -> False
  }
}

fn digit(c: Int) -> Bool {
  case c {
    x if x >= 48 && x <= 57 -> True
    _ -> False
  }
}

const underscore: Int = 95

const open_paren: Int = 40

fn ident_end(input: BitArray) -> BitArray {
  case input {
    <<x:size(8), rest:bytes>> -> {
      case alpha(x) || digit(x) || x == underscore {
        True -> ident_end(rest)
        False -> input
      }
    }
    _ -> input
  }
}

fn ident(input: BitArray) -> Result(#(BitArray, BitArray), Error) {
  case input {
    <<x:size(8), rest:bytes>> ->
      case alpha(x) || x == underscore {
        True -> {
          let rest = ident_end(rest)
          let v =
            slice(
              input,
              0,
              bit_array.byte_size(input) - bit_array.byte_size(rest),
            )
            |> result.lazy_unwrap(fn() { panic })
          Ok(#(v, trim_start(rest)))
        }
        False -> {
          // panic
          Error(ExpectedIdent(input))
        }
      }
    _ -> Error(ExpectedIdent(input))
  }
}

type Context =
  #(dict.Dict(BitArray, Int), Int)

fn with(cx: Context, v: BitArray) -> Context {
  #(dict.insert(cx.0, v, cx.1), cx.1 + 1)
}

fn parse_type(r: BitArray) -> Result(#(ast.Type, BitArray), Error) {
  use #(head, r) <- try(case r {
    <<"Unit":utf8, r:bytes>> -> Ok(#(ast.Unit, trim_start(r)))
    <<"Buffer":utf8, r:bytes>> -> Ok(#(ast.Buffer, trim_start(r)))
    <<"OutPointer":utf8, r:bytes>> -> Ok(#(ast.OutPointer, trim_start(r)))
    <<"Never":utf8, r:bytes>> -> Ok(#(ast.Never, trim_start(r)))
    <<"Pair":utf8, r:bytes>> -> {
      use #(left, r) <- try(parse_type(trim_start(r)))
      use #(right, r) <- try(parse_type(r))
      Ok(#(ast.Pair(left, right), r))
    }
    <<"Sum":utf8, r:bytes>> -> {
      use #(left, r) <- try(parse_type(trim_start(r)))
      use #(right, r) <- try(parse_type(r))
      Ok(#(ast.Sum(left, right), r))
    }
    <<"(":utf8, r:bytes>> -> {
      use #(inner, r) <- try(parse_type(trim_start(r)))
      case r {
        <<")":utf8, rest:bytes>> -> Ok(#(inner, rest))
        _ -> Error(Expected(<<")":utf8>>, r))
      }
    }
    _ -> Error(ExpectedType(r))
  })
  case r {
    <<"->":utf8, r:bytes>> -> {
      let r = trim_start(r)
      use #(mode, r) <- try(case r {
        <<"#":utf8, r:bytes>> -> {
          let r = trim_start(r)
          case r {
            <<"linear":utf8, r:bytes>> -> {
              Ok(#(ast.linear, trim_start(r)))
            }
            <<"affine":utf8, r:bytes>> -> {
              Ok(#(ast.affine, trim_start(r)))
            }
            <<"relevant":utf8, r:bytes>> -> {
              Ok(#(ast.relevant, trim_start(r)))
            }
            <<"normal":utf8, r:bytes>> -> {
              Ok(#(ast.normal, trim_start(r)))
            }
            _ -> Error(ExpectedStructure(r))
          }
        }
        _ -> Ok(#(ast.normal, r))
      })
      use #(ret, r) <- try(parse_type(r))
      Ok(#(ast.Fun(mode, head, ret), r))
    }
    _ -> Ok(#(head, r))
  }
}

const semi: Int = 0

const apply: Int = 1

const max: Int = 2

fn parse_expr_tail(
  cx: Context,
  r: BitArray,
  prec: Int,
  lhs: Expr,
) -> Result(#(Expr, BitArray), Error) {
  case r {
    <<";":utf8, r:bytes>> if prec <= semi -> {
      use #(rhs, r) <- try(parse_expr(with(cx, <<"">>), trim_start(r), semi))
      Ok(#(ast.Case(lhs, [#(ast.Bind, rhs)]), r))
    }
    _ if prec <= apply -> {
      case parse_expr(cx, r, max) {
        Ok(#(rhs, r)) -> parse_expr_tail(cx, r, prec, ast.App(lhs, rhs))
        Error(_) -> Ok(#(lhs, r))
      }
    }
    _ -> Ok(#(lhs, r))
  }
}

fn parse_expr(
  cx: Context,
  r: BitArray,
  prec: Int,
) -> Result(#(Expr, BitArray), Error) {
  use #(lhs, r) <- try(case r {
    <<"letpair":utf8, r:bytes>> -> {
      use #(n1, r) <- try(ident(trim_start(r)))
      use #(_, r) <- try(eat(<<",">>)(r))
      use #(n2, r) <- try(ident(r))
      use #(_, r) <- try(eat(<<"=">>)(r))
      use #(val, r) <- try(parse_expr(cx, r, apply))
      use #(_, r) <- try(eat(<<";">>)(r))
      use #(body, r) <- try(parse_expr(with(with(cx, n1), n2), r, semi))

      Ok(#(ast.Case(val, [#(ast.Cons, body)]), r))
    }
    <<"let":utf8, r:bytes>> -> {
      use #(n, r) <- try(ident(trim_start(r)))
      use #(_, r) <- try(eat(<<"=">>)(r))
      use #(val, r) <- try(parse_expr(cx, r, apply))
      use #(_, r) <- try(eat(<<";">>)(r))
      use #(body, r) <- try(parse_expr(with(cx, n), r, semi))

      Ok(#(ast.Case(val, [#(ast.Bind, body)]), r))
    }
    <<"case":utf8, r:bytes>> -> {
      use #(val, r) <- try(parse_expr(cx, trim_start(r), semi))
      use #(_, r) <- try(eat(<<"of">>)(r))
      use #(_, r) <- try(eat(<<"|">>)(r))
      use #(n1, r) <- try(ident(r))
      use #(_, r) <- try(eat(<<"=>">>)(r))
      use #(body1, r) <- try(parse_expr(with(cx, n1), r, apply))
      use #(_, r) <- try(eat(<<"|">>)(r))
      use #(n2, r) <- try(ident(r))
      use #(_, r) <- try(eat(<<"=>">>)(r))
      use #(body2, r) <- try(parse_expr(with(cx, n2), r, semi))

      Ok(#(
        ast.Case(val, [
          #(ast.Left, body1),
          #(ast.Right, body2),
        ]),
        r,
      ))
    }
    <<"break":utf8, r:bytes>> -> {
      use #(e, r) <- try(parse_expr(cx, trim_start(r), apply))
      Ok(#(ast.Jump(ast.Break, e), r))
    }
    <<"continue":utf8, r:bytes>> -> {
      use #(e, r) <- try(parse_expr(cx, trim_start(r), apply))
      Ok(#(ast.Jump(ast.Continue, e), r))
    }
    <<"fun":utf8, r:bytes>> -> {
      use #(param, r) <- try(ident(trim_start(r)))
      use #(_, r) <- try(eat(<<":">>)(r))
      use #(typ, r) <- try(parse_type(r))
      use #(_, r) <- try(eat(<<"=>">>)(r))
      use #(body, r) <- try(parse_expr(with(cx, param), r, apply))

      Ok(#(ast.Lam(typ, body), r))
    }
    <<"loop":utf8, r:bytes>> -> {
      use #(n, r) <- try(ident(trim_start(r)))
      use #(_, r) <- try(eat(<<"from">>)(r))
      use #(e, r) <- try(parse_expr(cx, r, semi))
      use #(_, r) <- try(eat(<<"in">>)(r))
      use #(body, r) <- try(parse_expr(with(cx, n), r, apply))
      Ok(#(ast.Loop(e, body), r))
    }
    <<"(":utf8, r:bytes>> -> {
      use #(e, r) <- try(parse_expr(cx, r, semi))
      use #(_, r) <- try(eat(<<")">>)(r))
      Ok(#(e, r))
    }
    _ -> {
      use #(name, r) <- try(ident(r))
      use n <- try(
        dict.get(cx.0, name)
        |> result.map_error(fn(_) { UndefinedVariable(name, r) }),
      )
      Ok(#(ast.Var({ cx.1 - 1 } - n), r))
    }
  })
  parse_expr_tail(cx, r, prec, lhs)
}

pub fn parse(input: BitArray) -> Result(Expr, Error) {
  use #(expr, r) <- try(parse_expr(#(dict.new(), 0), trim_start(input), semi))
  use <- bool.guard(r != <<>>, Error(ExpectedEof(r)))
  Ok(expr)
}
