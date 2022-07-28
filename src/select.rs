use super::shape::*;

pub trait Selector {
    #![allow(unused)]
    fn annotate(&self, uuid: &Uuid, expr: &Expression) {}
    fn base(&self, uuid: &Uuid, exprs: &Vec<Expression>) {}
    fn record(&self, fields: &Vec<(String, Expression)>) {}
    fn variant(&self, alts: &Vec<(String, Vec<Expression>)>) {}
    fn tuple(&self, elems: &Vec<Expression>) {}
    fn poly_variant(&self, loc: &Location, constrs: &Vec<PolyConstr>) {}
    fn var(&self, loc: &Location, vid: &Vid) {}
    fn rec_app(&self, tid: &Tid, args: &Vec<Expression>) {}
    fn top_app(&self, group: &Group, tid: &Tid, args: &Vec<Expression>) {}
}

pub trait MutSelector {
    #![allow(unused)]
    fn annotate(&mut self, uuid: &Uuid, expr: &Expression) {}
    fn base(&mut self, uuid: &Uuid, exprs: &Vec<Expression>) {}
    fn record(&mut self, fields: &Vec<(String, Expression)>) {}
    fn variant(&mut self, alts: &Vec<(String, Vec<Expression>)>) {}
    fn tuple(&mut self, elems: &Vec<Expression>) {}
    fn poly_variant(&mut self, loc: &Location, constrs: &Vec<PolyConstr>) {}
    fn var(&mut self, loc: &Location, vid: &Vid) {}
    fn rec_app(&mut self, tid: &Tid, args: &Vec<Expression>) {}
    fn top_app(&mut self, group: &Group, tid: &Tid, args: &Vec<Expression>) {}
}

pub trait ValueSelector<T> {
    #![allow(unused)]
    fn default_result(&self) -> T;
    fn annotate(&self, uuid: &Uuid, expr: &Expression) -> T {
        self.default_result()
    }
    fn base(&self, uuid: &Uuid, exprs: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn record(&self, fields: &Vec<(String, Expression)>) -> T {
        self.default_result()
    }
    fn variant(&self, alts: &Vec<(String, Vec<Expression>)>) -> T {
        self.default_result()
    }
    fn tuple(&self, elems: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn poly_variant(&self, loc: &Location, constrs: &Vec<PolyConstr>) -> T {
        self.default_result()
    }
    fn var(&self, loc: &Location, vid: &Vid) -> T {
        self.default_result()
    }
    fn rec_app(&self, tid: &Tid, args: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn top_app(&self, group: &Group, tid: &Tid, args: &Vec<Expression>) -> T {
        self.default_result()
    }
}

pub trait ValueMutSelector<T> {
    #![allow(unused)]
    fn default_result(&mut self) -> T;
    fn annotate(&mut self, uuid: &Uuid, expr: &Expression) -> T {
        self.default_result()
    }
    fn base(&mut self, uuid: &Uuid, exprs: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn record(&mut self, fields: &Vec<(String, Expression)>) -> T {
        self.default_result()
    }
    fn variant(&mut self, alts: &Vec<(String, Vec<Expression>)>) -> T {
        self.default_result()
    }
    fn tuple(&mut self, elems: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn poly_variant(&mut self, loc: &Location, constrs: &Vec<PolyConstr>) -> T {
        self.default_result()
    }
    fn var(&mut self, loc: &Location, vid: &Vid) -> T {
        self.default_result()
    }
    fn rec_app(&mut self, tid: &Tid, args: &Vec<Expression>) -> T {
        self.default_result()
    }
    fn top_app(&mut self, group: &Group, tid: &Tid, args: &Vec<Expression>) -> T {
        self.default_result()
    }
}

pub trait Selecting {
    fn select<T: Selector>(&self, s: &T);
}

impl Selecting for Expression {
    fn select<T>(&self, selector: &T)
    where
        T: Selector,
    {
        match self {
            Expression::Annotate(uuid, expr) => selector.annotate(uuid, expr),
            Expression::Base(uuid, exprs) => selector.base(uuid, exprs),
            Expression::Record(fields) => selector.record(fields),
            Expression::Variant(alts) => selector.variant(alts),
            Expression::Tuple(elems) => selector.tuple(elems),
            Expression::Poly_variant((loc, constrs)) => selector.poly_variant(loc, constrs),
            Expression::Var((loc, vid)) => selector.var(loc, vid),
            Expression::Rec_app(tid, args) => selector.rec_app(tid, args),
            Expression::Top_app(group, tid, args) => selector.top_app(group, tid, args),
        }
    }
}

pub trait SelectingMut {
    fn select_mut<T: MutSelector>(&self, s: &mut T);
}

impl SelectingMut for Expression {
    fn select_mut<T>(&self, selector: &mut T)
    where
        T: MutSelector,
    {
        match self {
            Expression::Annotate(uuid, expr) => selector.annotate(uuid, expr),
            Expression::Base(uuid, exprs) => selector.base(uuid, exprs),
            Expression::Record(fields) => selector.record(fields),
            Expression::Variant(alts) => selector.variant(alts),
            Expression::Tuple(elems) => selector.tuple(elems),
            Expression::Poly_variant((loc, constrs)) => selector.poly_variant(loc, constrs),
            Expression::Var((loc, vid)) => selector.var(loc, vid),
            Expression::Rec_app(tid, args) => selector.rec_app(tid, args),
            Expression::Top_app(group, tid, args) => selector.top_app(group, tid, args),
        }
    }
}

pub trait SelectingWithValue {
    fn select_with_value<T: ValueSelector<V>, V>(&self, s: &T) -> V;
}

impl SelectingWithValue for Expression {
    fn select_with_value<T, V>(&self, selector: &T) -> V
    where
        T: ValueSelector<V>,
    {
        match self {
            Expression::Annotate(uuid, expr) => selector.annotate(uuid, expr),
            Expression::Base(uuid, exprs) => selector.base(uuid, exprs),
            Expression::Record(fields) => selector.record(fields),
            Expression::Variant(alts) => selector.variant(alts),
            Expression::Tuple(elems) => selector.tuple(elems),
            Expression::Poly_variant((loc, constrs)) => selector.poly_variant(loc, constrs),
            Expression::Var((loc, vid)) => selector.var(loc, vid),
            Expression::Rec_app(tid, args) => selector.rec_app(tid, args),
            Expression::Top_app(group, tid, args) => selector.top_app(group, tid, args),
        }
    }
}

pub trait SelectingMutWithValue {
    fn select_mut_with_value<T: ValueMutSelector<V>, V>(&self, s: &mut T) -> V;
}

impl SelectingMutWithValue for Expression {
    fn select_mut_with_value<T, V>(&self, selector: &mut T) -> V
    where
        T: ValueMutSelector<V>,
    {
        match self {
            Expression::Annotate(uuid, expr) => selector.annotate(uuid, expr),
            Expression::Base(uuid, exprs) => selector.base(uuid, exprs),
            Expression::Record(fields) => selector.record(fields),
            Expression::Variant(alts) => selector.variant(alts),
            Expression::Tuple(elems) => selector.tuple(elems),
            Expression::Poly_variant((loc, constrs)) => selector.poly_variant(loc, constrs),
            Expression::Var((loc, vid)) => selector.var(loc, vid),
            Expression::Rec_app(tid, args) => selector.rec_app(tid, args),
            Expression::Top_app(group, tid, args) => selector.top_app(group, tid, args),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        select::{MutSelector, SelectingMut, SelectingWithValue, ValueSelector},
        shape::Expression,
    };

    fn simple_top_app() -> Expression {
        r#"
(Top_app
 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#
            .parse()
            .unwrap()
    }

    fn base() -> Expression {
        r#"(Base kimchi_backend_bigint_32_V1 ())"#.parse().unwrap()
    }

    #[test]
    fn select_mut() {
        struct S(bool);
        impl MutSelector for S {
            fn top_app(
                &mut self,
                _group: &crate::shape::Group,
                _tid: &crate::shape::Tid,
                _args: &Vec<crate::shape::Expression>,
            ) {
                self.0 = true;
            }
        }

        let mut s = S(false);
        simple_top_app().select_mut(&mut s);
        assert!(s.0);

        let mut s = S(false);
        base().select_mut(&mut s);
        assert!(!s.0);
    }

    #[test]
    fn select_with_value() {
        struct S;
        impl ValueSelector<bool> for S {
            fn top_app(
                &self,
                _group: &crate::shape::Group,
                _tid: &crate::shape::Tid,
                _args: &Vec<crate::shape::Expression>,
            ) -> bool {
                true
            }

            fn default_result(&self) -> bool {
                false
            }
        }

        assert!(simple_top_app().select_with_value(&S));
        assert!(!base().select_with_value(&S));
    }
}
