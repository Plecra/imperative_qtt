fn main() {
    let mut context = std::collections::HashMap::new();
    let mut skips = 0;
    let unit_ty = imperative_qtt::Ty::Unit.rc();
    let mut errors = Vec::new();
    let prec = 0;
    let sources = &[
        "fun foo => fun bar => foo bar",
        // "fun foo : (() -> ()) => fun x : () => foo x",
        "fun foo : () -> () => fun x : () => loop (break (foo x))",
        "fun foo : Sum () () => case foo of x => x | y => loop break y",
        "fun foo : Pair () () => fun mkpair : () -> () -> Pair () () =>
            let [a, b] = foo;
            mkpair a b",

    ];
    for source in sources {
        let ast = imperative_qtt::parse_expr(&mut source.as_bytes(), &mut context, &mut skips, &unit_ty, &mut errors, prec);
        println!("{:?}", ast);
        let result = imperative_qtt::infer(&ast);
        println!("{:?}", result);
    }
}