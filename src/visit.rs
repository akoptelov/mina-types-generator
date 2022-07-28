use crate::shape::*;

pub trait Visitor<'a>: Sized {
    /// Apply this visitor to the specified expression `expr`.
    ///
    /// By default just visit all sub-expressions with the visitor.
    fn apply(&mut self, expr: &'a Expression) {
        expr.visit(self)
    }
}

pub trait Visiting<'a> {
    fn visit<V: Visitor<'a>>(&'a self, visitor: &mut V);
}

impl<'a, T> Visiting<'a> for Box<T>
where
    T: Visiting<'a>,
{
    fn visit<V: Visitor<'a>>(&'a self, visitor: &mut V) {
        self.as_ref().visit(visitor)
    }
}

impl<'a> Visiting<'a> for Expression {
    fn visit<V>(&'a self, visitor: &mut V)
    where
        V: Visitor<'a>,
    {
        let mut app = |expr: &'a Expression| visitor.apply(expr);
        match self {
            Expression::Annotate(_, expr) => app(expr),
            Expression::Base(_, exprs) => exprs.iter().for_each(app),
            Expression::Record(fields) => fields.iter().map(|(_, expr)| expr).for_each(app),
            Expression::Variant(alternatives) => alternatives
                .iter()
                .map(|(_, expr)| expr.iter())
                .flatten()
                .for_each(app),
            Expression::Tuple(exprs) => exprs.iter().for_each(app),
            Expression::Poly_variant((_, constrs)) => {
                constrs.iter().for_each(|constr| constr.visit(visitor))
            }
            Expression::Var(_) => (),
            Expression::Rec_app(_, exprs) => exprs.iter().for_each(app),
            Expression::Top_app(group, _, exprs) => {
                exprs.iter().for_each(app);
                group.visit(visitor);
            }
        }
    }
}

impl<'a> Visiting<'a> for Group {
    fn visit<V>(&'a self, visitor: &mut V)
    where
        V: Visitor<'a>,
    {
        let app = |expr| visitor.apply(expr);
        self.members.iter().map(|(_, (_, expr))| expr).for_each(app);
    }
}

impl<'a> Visiting<'a> for PolyConstr {
    fn visit<V>(&'a self, visitor: &mut V)
    where
        V: Visitor<'a>,
    {
        let mut app = |expr| visitor.apply(expr);
        match self {
            PolyConstr::Constr((_, expr)) => expr.iter().map(|b| b.as_ref()).for_each(app),
            PolyConstr::Inherit((_, expr)) => app(expr),
        }
    }
}

#[cfg(test)]
mod visitor_tests {
    use crate::{
        shape::Expression,
        visit::{Visiting, Visitor},
    };

    #[test]
    fn deep_visitor() {
        let expr = r#"
(Top_app
 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#
            .parse()
            .unwrap();

        struct Vis(usize);
        impl<'a> Visitor<'a> for Vis {
            fn apply(&mut self, expr: &'a Expression) {
                self.0 += 1;
                expr.visit(self)
            }
        }

        let mut v = Vis(0);
        v.apply(&expr);
        assert_eq!(v.0, 2);

        let mut v = Vis(0);
        expr.visit(&mut v);
        assert_eq!(v.0, 1);
    }

    #[test]
    fn shallow_visitor() {
        let expr = r#"
(Top_app
 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#
            .parse()
            .unwrap();

        struct Vis(Option<Expression>);
        impl<'a> Visitor<'a> for Vis {
            fn apply(&mut self, expr: &'a Expression) {
                self.0 = Some(expr.clone());
            }
        }

        let mut v = Vis(None);
        v.apply(&expr);
        assert!(matches!(v.0, Some(Expression::Top_app(..))));

        let mut v = Vis(None);
        expr.visit(&mut v);
        assert!(matches!(v.0, Some(Expression::Base(..))));
    }
}

impl<'a, F> Visitor<'a> for F
where
    F: FnMut(&'a Expression),
{
    fn apply(&mut self, expr: &'a Expression) {
        self(expr)
    }
}

/// Visitor that yields a value.
///
/// Values from multiple expressions are folded into a single one.
pub trait ValueVisitor<'a, T> {
    /// Applies this visitor to the `expr`, producing some value.
    fn apply(&self, expr: &'a Expression) -> T;
    /// Folds the value `value` obtained from applying it to an expreesion
    /// with the accumulator `acc`, returning the result.
    fn fold(&self, acc: T, value: T) -> T;
}

pub trait ValueVisiting<'a> {
    fn visit_with_value<V, R>(&'a self, visitor: &V) -> Option<R>
    where
        V: ValueVisitor<'a, R>;
}

impl<'a> ValueVisiting<'a> for Expression {
    fn visit_with_value<V, R>(&'a self, visitor: &V) -> Option<R>
    where
        V: ValueVisitor<'a, R>,
    {
        let app = |expr| visitor.apply(expr);
        let reduce = |a, v| visitor.fold(a, v);
        match self {
            Expression::Annotate(_, expr) => Some(app(expr)),
            Expression::Base(_, exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Record(fields) => {
                fields.iter().map(|(_, expr)| expr).map(app).reduce(reduce)
            }
            Expression::Variant(alternatives) => alternatives
                .iter()
                .map(|(_, expr)| expr.iter())
                .flatten()
                .map(app)
                .reduce(reduce),
            Expression::Tuple(exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Poly_variant((_, constrs)) => constrs
                .iter()
                .filter_map(|constr| constr.visit_with_value(visitor))
                .reduce(reduce),
            Expression::Var(_) => None,
            Expression::Rec_app(_, exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Top_app(group, _, exprs) => {
                let v1 = exprs.iter().map(app).reduce(reduce);
                let v2: Option<R> = group.visit_with_value(visitor);
                //v1.zip_with(v2, |v1, v2| visitor.fold(v1, v2)).or_else(|| v1.or(v2))
                match (v1, v2) {
                    (Some(v1), Some(v2)) => Some(visitor.fold(v1, v2)),
                    (Some(v1), _) => Some(v1),
                    (_, Some(v2)) => Some(v2),
                    _ => None,
                }
            }
        }
    }
}

impl<'a> ValueVisiting<'a> for Group {
    fn visit_with_value<V, R>(&'a self, visitor: &V) -> Option<R>
    where
        V: ValueVisitor<'a, R>,
    {
        let app = |expr| visitor.apply(expr);
        let reduce = |a, v| visitor.fold(a, v);
        self.members
            .iter()
            .map(|(_, (_, expr))| expr)
            .map(app)
            .reduce(reduce)
    }
}

impl<'a> ValueVisiting<'a> for PolyConstr {
    fn visit_with_value<V, R>(&'a self, visitor: &V) -> Option<R>
    where
        V: ValueVisitor<'a, R>,
    {
        let app = |expr| visitor.apply(expr);
        let reduce = |a, v| visitor.fold(a, v);
        match self {
            PolyConstr::Constr((_, expr)) => {
                expr.iter().map(|b| b.as_ref()).map(app).reduce(reduce)
            }
            PolyConstr::Inherit((_, expr)) => Some(app(expr)),
        }
    }
}

#[cfg(test)]
mod visitor_with_value_tests {
    use crate::{
        shape::Expression,
        visit::{ValueVisiting, ValueVisitor},
    };

    #[test]
    fn deep_visitor() {
        let expr = r#"
(Top_app
 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#
            .parse()
            .unwrap();

        struct Vis;
        impl<'a> ValueVisitor<'a, usize> for Vis {
            fn apply(&self, expr: &'a Expression) -> usize {
                expr.visit_with_value(self).map_or(1, |v| v + 1)
            }

            fn fold(&self, acc: usize, value: usize) -> usize {
                acc + value
            }
        }

        let v = Vis;
        assert_eq!(v.apply(&expr), 2);

        let v = Vis;
        assert_eq!(expr.visit_with_value(&v), Some(1));
    }

    #[test]
    fn shallow_visitor() {
        let expr = r#"
(Top_app
 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#
            .parse()
            .unwrap();

        struct Vis;
        impl<'a> ValueVisitor<'a, Expression> for Vis {
            fn apply(&self, expr: &'a Expression) -> Expression {
                expr.clone()
            }

            fn fold(&self, _acc: Expression, value: Expression) -> Expression {
                value
            }
        }

        let v = Vis;
        v.apply(&expr);
        assert!(matches!(v.apply(&expr), Expression::Top_app(..)));

        let v = Vis;
        assert!(matches!(expr.visit_with_value(&v), Some(Expression::Base(..))));
    }
}


/// Visitor that yields a value.
///
/// Values from multiple expressions are folded into a single one.
pub trait ValueMutVisitor<'a, T, F> {
    /// Applies this visitor to the `expr`, producing some value.
    fn apply(&mut self, expr: &'a Expression, f: &F) -> T;
    // /// Folds the value `value` obtained from applying it to an expreesion
    // /// with the accumulator `acc`, returning the result.
    // fn fold(acc: T, value: T) -> T;
}

pub trait ValueMutVisiting<'a> {
    fn visit_mut_with_value<V, R, F>(&'a self, visitor: &mut V, reduce: &F) -> Option<R>
    where
        V: ValueMutVisitor<'a, R, F>,
        F: Fn(R, R) -> R;
}

impl<'a> ValueMutVisiting<'a> for Expression {
    fn visit_mut_with_value<V, R, F>(&'a self, visitor: &mut V, reduce: &F) -> Option<R>
    where
        V: ValueMutVisitor<'a, R, F>,
        F: Fn(R, R) -> R,
    {
        let mut app = |expr| visitor.apply(expr, reduce);
        match self {
            Expression::Annotate(_, expr) => Some(app(expr)),
            Expression::Base(_, exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Record(fields) => {
                fields.iter().map(|(_, expr)| expr).map(app).reduce(reduce)
            }
            Expression::Variant(alternatives) => alternatives
                .iter()
                .map(|(_, expr)| expr.iter())
                .flatten()
                .map(app)
                .reduce(reduce),
            Expression::Tuple(exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Poly_variant((_, constrs)) => constrs
                .iter()
                .filter_map(|constr| constr.visit_mut_with_value(visitor, reduce))
                .reduce(reduce),
            Expression::Var(_) => None,
            Expression::Rec_app(_, exprs) => exprs.iter().map(app).reduce(reduce),
            Expression::Top_app(group, _, exprs) => {
                let v1 = exprs.iter().map(app).reduce(reduce);
                let v2: Option<R> = group.visit_mut_with_value(visitor, reduce);
                //v1.zip_with(v2, |v1, v2| visitor.fold(v1, v2)).or_else(|| v1.or(v2))
                match (v1, v2) {
                    (Some(v1), Some(v2)) => Some(reduce(v1, v2)),
                    (Some(v1), _) => Some(v1),
                    (_, Some(v2)) => Some(v2),
                    _ => None,
                }
            }
        }
    }
}

impl<'a> ValueMutVisiting<'a> for Group {
    fn visit_mut_with_value<V, R, F>(&'a self, visitor: &mut V, reduce: &F) -> Option<R>
    where
        V: ValueMutVisitor<'a, R, F>,
        F: Fn(R, R) -> R,
    {
        let app = |expr| visitor.apply(expr, reduce);
        self.members
            .iter()
            .map(|(_, (_, expr))| expr)
            .map(app)
            .reduce(reduce)
    }
}

impl<'a> ValueMutVisiting<'a> for PolyConstr {
    fn visit_mut_with_value<V, R, F>(&'a self, visitor: &mut V, reduce: &F) -> Option<R>
    where
        V: ValueMutVisitor<'a, R, F>,
        F: Fn(R, R) -> R,
    {
        let mut app = |expr| visitor.apply(expr, reduce);
        match self {
            PolyConstr::Constr((_, expr)) => {
                expr.iter().map(|b| b.as_ref()).map(app).reduce(reduce)
            }
            PolyConstr::Inherit((_, expr)) => Some(app(expr)),
        }
    }
}
