mod infer;
mod parse;
mod ast;
pub use parse::parse_expr;
pub use infer::InferError;
pub use ast::{Expr, Ty};

pub fn infer(expr: &ast::ExprNode) -> (infer::Exits, Vec<InferError>) {
    let mut st = infer::InferState {
        locals: Vec::new(),
        errors: Vec::new(),
    };
    let unit_ty = ast::Ty::Unit.rc();
    (infer::infer(&mut st, &unit_ty, expr), st.errors)
}


use std::collections::HashMap;
trait HashMapExt<K, V> {
    fn set(&mut self, key: K, value: Option<V>);
}

impl<K: std::cmp::Eq + std::hash::Hash, V> HashMapExt<K, V> for HashMap<K, V> {
    fn set(&mut self, key: K, value: Option<V>) {
        if let Some(value) = value {
            self.insert(key, value);
        } else {
            self.remove(&key);
        }
    }
}