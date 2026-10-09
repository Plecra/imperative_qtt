import ast
import gleam/bit_array
import gleam/dict
import gleam/io
import gleam/list
import gleam/result.{try}
import gleam/string
import infer
import iv
import parse
import simplifile

fn unwrap_or_else(r: Result(a, b), f: fn(b) -> a) -> a {
  case r {
    Ok(v) -> v
    Error(e) -> f(e)
  }
}

fn dump(a: Result(a, b), context: String) -> Result(a, Nil) {
  case a {
    Ok(v) -> Ok(v)
    Error(e) -> {
      echo #(context, e)
      Error(Nil)
    }
  }
}

fn digits(n: Int) -> BitArray {
  case n < 10 {
    True -> <<{ n % 10 + 48 }:size(8)>>
    False -> <<{ n % 10 + 48 }:size(8), digits(n / 10):bits>>
  }
}

const arrow: Int = 0

const apply: Int = 1

const atom: Int = 2

fn prec(s: #(String, Int), at: Int) -> String {
  case at <= s.1 {
    True -> s.0
    False -> string.join(["(", s.0, ")"], "")
  }
}

fn print_type(t: ast.Type) -> #(String, Int) {
  case t {
    ast.Unit -> #("Unit", atom)
    ast.OutPointer -> #("OutPointer", atom)
    ast.Never -> #("Never", atom)
    ast.Buffer -> #("Buffer", atom)
    ast.Sum(a, b) -> #(
      string.join(
        ["Sum ", print_type(a) |> prec(atom), " ", print_type(b) |> prec(atom)],
        "",
      ),
      apply,
    )
    ast.Pair(a, b) -> #(
      string.join(
        [
          "Pair ",
          print_type(a) |> prec(atom),
          " ",
          print_type(b) |> prec(atom),
        ],
        "",
      ),
      apply,
    )
    ast.Fun(m, a, b) -> #(
      string.join(
        [
          print_type(a) |> prec(apply),
          " -> # ",
          case m {
            ast.Desc(True, True) -> "normal"
            ast.Desc(True, False) -> "relevant"
            ast.Desc(False, True) -> "affine"
            ast.Desc(False, False) -> "linear"
          },
          " ",
          print_type(b) |> prec(arrow),
        ],
        "",
      ),
      arrow,
    )
  }
}

fn nth(l: List(a), n: Int) -> Result(a, Nil) {
  case l {
    [] -> Error(Nil)
    [x, ..xs] ->
      case n {
        0 -> Ok(x)
        _ -> nth(xs, n - 1)
      }
  }
}

const indent: Int = 2

fn print_error(
  names: iv.Array(BitArray),
  e: ast.Expr,
  depth: Int,
  loc: Result(infer.Loc, Nil),
) {
  case loc == Ok(infer.Here) {
    True -> io.print("[[")
    False -> Nil
  }
  case e {
    ast.Var(n) -> {
      io.print(
        bit_array.to_string(
          iv.get(names, iv.size(names) - 1 - n)
          |> result.lazy_unwrap(fn() { panic }),
        )
        |> result.lazy_unwrap(fn() { panic }),
      )
    }
    ast.Lam(t, b) -> {
      let name = <<"x":utf8, digits(iv.size(names)):bits>>
      io.print("fun ")
      io.print(bit_array.to_string(name) |> result.lazy_unwrap(fn() { panic }))
      io.print(" : ")
      io.print(print_type(t) |> prec(arrow))
      io.print(" =>\n")
      io.print(string.repeat(" ", depth + indent))
      print_error(iv.append(names, name), b, depth + indent, case loc {
        Ok(infer.Child(0, l)) -> Ok(l)
        _ -> Error(Nil)
      })
    }
    ast.Loop(init, body) -> {
      let loopname = <<"x":utf8, digits(iv.size(names)):bits>>
      let name = <<"x":utf8, digits(iv.size(names) + 2):bits>>
      io.print("loop :")
      io.print(
        bit_array.to_string(loopname) |> result.lazy_unwrap(fn() { panic }),
      )
      io.print(" ")
      io.print(bit_array.to_string(name) |> result.lazy_unwrap(fn() { panic }))
      io.print(" from ")
      let _ =
        print_error(names, init, depth + indent, case loc {
          Ok(infer.Child(0, l)) -> Ok(l)
          _ -> Error(Nil)
        })
      io.print(" in\n")
      io.print(string.repeat(" ", depth + indent))
      print_error(
        iv.append(
          names
            |> iv.append(<<"continue :":utf8, loopname:bits, " ":utf8>>)
            |> iv.append(<<"break :":utf8, loopname:bits, " ":utf8>>),
          name,
        ),
        body,
        depth + indent,
        case loc {
          Ok(infer.Child(1, l)) -> Ok(l)
          _ -> Error(Nil)
        },
      )
    }
    ast.Case(scrutinee, branches) -> {
      case list.length(branches) {
        1 -> {
          let #(p, e) =
            list.first(branches) |> result.lazy_unwrap(fn() { panic })
          case p {
            ast.Bind -> {
              let name = <<"x":utf8, digits(iv.size(names)):bits>>
              io.print("let ")
              io.print(
                bit_array.to_string(name) |> result.lazy_unwrap(fn() { panic }),
              )
              io.print(" = ")
              let _ =
                print_error(names, scrutinee, depth + indent, case loc {
                  Ok(infer.Child(0, l)) -> Ok(l)
                  _ -> Error(Nil)
                })
              io.print(";\n")
              io.print(string.repeat(" ", depth))
              print_error(iv.append(names, name), e, depth, case loc {
                Ok(infer.Child(1, l)) -> Ok(l)
                _ -> Error(Nil)
              })
            }
            ast.Cons -> {
              let name = <<"x":utf8, digits(iv.size(names)):bits>>
              let name2 = <<"x":utf8, digits(iv.size(names) + 1):bits>>
              io.print("letpair ")
              io.print(
                bit_array.to_string(name) |> result.lazy_unwrap(fn() { panic }),
              )
              io.print(", ")
              io.print(
                bit_array.to_string(name2) |> result.lazy_unwrap(fn() { panic }),
              )
              io.print(" = ")
              let _ =
                print_error(names, scrutinee, depth + indent, case loc {
                  Ok(infer.Child(0, l)) -> Ok(l)
                  _ -> Error(Nil)
                })
              io.print(";\n")
              io.print(string.repeat(" ", depth))
              print_error(
                iv.append(iv.append(names, name), name2),
                e,
                depth,
                case loc {
                  Ok(infer.Child(1, l)) -> Ok(l)
                  _ -> Error(Nil)
                },
              )
            }
            _ -> panic
          }
        }
        2 -> {
          io.print("case ")
          let _ =
            print_error(names, scrutinee, depth + indent, case loc {
              Ok(infer.Child(0, l)) -> Ok(l)
              _ -> Error(Nil)
            })
          io.print(" of\n")
          io.print(string.repeat(" ", depth))
          let name = <<"x":utf8, digits(iv.size(names)):bits>>
          let name_txt =
            bit_array.to_string(name) |> result.lazy_unwrap(fn() { panic })
          io.print("| ")
          io.print(name_txt)
          io.print(" => ")
          print_error(
            iv.append(names, name),
            { branches |> nth(0) |> result.lazy_unwrap(fn() { panic }) }.1,
            depth + indent,
            case loc {
              Ok(infer.Child(1, l)) -> Ok(l)
              _ -> Error(Nil)
            },
          )
          io.print("\n")
          io.print(string.repeat(" ", depth))

          io.print("| ")
          io.print(name_txt)
          io.print(" => ")
          print_error(
            iv.append(names, name),
            { branches |> nth(1) |> result.lazy_unwrap(fn() { panic }) }.1,
            depth + indent,
            case loc {
              Ok(infer.Child(2, l)) -> Ok(l)
              _ -> Error(Nil)
            },
          )
        }
        _ -> panic
      }
    }
    ast.Jump(target, e) -> {
      io.print(
        bit_array.to_string(
          iv.get(names, iv.size(names) - 1 - target)
          |> result.lazy_unwrap(fn() { panic }),
        )
        |> result.lazy_unwrap(fn() { panic }),
      )
      print_error(names, e, depth + indent, case loc {
        Ok(infer.Child(0, l)) -> Ok(l)
        _ -> Error(Nil)
      })
    }
    ast.App(f, args) -> {
      io.print("(")
      let _ =
        print_error(names, f, depth, case loc {
          Ok(infer.Child(0, l)) -> Ok(l)
          _ -> Error(Nil)
        })
      io.print(")")
      io.print(" ")
      io.print("(")
      let _ =
        print_error(names, args, depth, case loc {
          Ok(infer.Child(1, l)) -> Ok(l)
          _ -> Error(Nil)
        })
      io.print(")")
    }
  }
  case loc == Ok(infer.Here) {
    True -> io.print("]]")
    False -> Nil
  }
}

pub fn main() -> Nil {
  use e <- unwrap_or_else({
    use a <- try(
      simplifile.read_directory("examples")
      |> dump("Reading examples directory"),
    )
    use _ <- try(
      list.try_each(a, fn(x) {
        use content <- try(
          simplifile.read_bits(string.append("examples/", x))
          |> dump("Reading file content"),
        )
        use expr <- try(parse.parse(content) |> dump("Parsing content"))
        echo expr
        case infer.infer(dict.new(), expr) {
          Ok(t) -> {
            echo #("good code")
            Ok(Nil)
          }
          Error(#(e, loc)) -> {
            echo e
            print_error(iv.new(), expr, 0, Ok(loc))
            io.println("")
            Error(Nil)
          }
        }
      }),
    )
    Ok(Nil)
  })
  io.println("Exiting with error...")
}
//Child(0, Child(0, Child(0, Child(0, Child(0, Child(0, Child(1, Child(0, Here))))))))
