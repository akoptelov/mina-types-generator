use std::str::FromStr;

use derive_new::new;
use rsexp::OfSexp;
use rsexp_derive::{OfSexp, SexpOf};
use thiserror::Error;

pub type Gid = i32;
pub type Location = String;
pub type Tid = String;
pub type Vid = String;
pub type Uuid = String;


pub trait Visitor<'a> {
    /// Apply this visitor to the specified expression `expr`.
    ///
    /// By default just visit all sub-expressions with the visitor.
    fn apply(&mut self, expr: &'a Expression);
}

impl<'a, T> Visitor<'a> for T
where
    T: FnMut(&'a Expression),
{
    fn apply(&mut self, expr: &'a Expression) {
        self(expr)
    }
}

#[derive(Debug, Clone, OfSexp, SexpOf)]
pub struct Group {
    pub gid: Gid,
    pub loc: Location,
    pub members: Vec<(Tid, (Vec<Vid>, Expression))>,
}

impl Group {
    fn visit<'a, T>(&'a self, visitor: &mut T)
    where
        T: Visitor<'a>,
    {
        let app = |expr| visitor.apply(expr);
        self.members.iter().map(|(_, (_, expr))| expr).for_each(app);
    }
}

#[derive(Debug, Clone, OfSexp, SexpOf, new)]
pub enum Expression {
    Annotate(Uuid, Box<Expression>),
    Base(Uuid, Vec<Expression>),
    Record(Vec<(String, Expression)>),
    Variant(Vec<(String, Vec<Expression>)>),
    Tuple(Vec<Expression>),
    #[sexp_rename("Poly_variant")]
    #[allow(non_camel_case_types)]
    Poly_variant((Location, Vec<PolyConstr>)),

    Var((Location, Vid)),
    #[sexp_rename("Rec_app")]
    #[allow(non_camel_case_types)]
    Rec_app(Tid, Vec<Expression>),
    #[sexp_rename("Top_app")]
    #[allow(non_camel_case_types)]
    Top_app(Group, Tid, Vec<Expression>),
}

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

impl Expression {
    pub fn visit<'a, T>(&'a self, visitor: &mut T)
    where
        T: Visitor<'a>,
    {
        let mut app = |expr| visitor.apply(expr);
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
            },
        }
    }

    pub fn select<T>(&self, selector: &T) where T: Selector {
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

    pub fn select_mut<T>(&self, selector: &mut T) where T: MutSelector {
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

#[derive(Debug, Clone, OfSexp, SexpOf)]
pub enum PolyConstr {
    Constr((String, Option<Box<Expression>>)),
    Inherit((Location, Box<Expression>)),
}

impl PolyConstr {
    fn visit<'a, T>(&'a self, visitor: &mut T)
    where
        T: Visitor<'a>,
    {
        let mut app = |expr| visitor.apply(expr);
        match self {
            PolyConstr::Constr((_, expr)) => expr.iter().map(|b| b.as_ref()).for_each(app),
            PolyConstr::Inherit((_, expr)) => app(expr),
        }
    }
}

#[derive(Debug, Error)]
pub enum FromStrError {
    #[error("error parsing sexp: {0}")]
    Sexp(#[from] rsexp::Error),
    #[error("error building expression from sexp: {0}")]
    OfSexp(#[from] rsexp::IntoSexpError),
}

impl FromStr for Expression {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let sexp = rsexp::from_slice(s)?;
        let expr = <Self as OfSexp>::of_sexp(&sexp)?;
        Ok(expr)
    }
}

impl FromStr for PolyConstr {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let sexp = rsexp::from_slice(s)?;
        let expr = <Self as OfSexp>::of_sexp(&sexp)?;
        Ok(expr)
    }
}

impl FromStr for Group {
    type Err = FromStrError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let sexp = rsexp::from_slice(s)?;
        let expr = <Self as OfSexp>::of_sexp(&sexp)?;
        Ok(expr)
    }
}

#[cfg(test)]
mod tests {
    use super::{Expression, PolyConstr};

    use rsexp::{OfSexp, SexpOf};

    #[test]
    fn test_base() {
        let sexp = r#"(Base t ())"#;
        let sexp = rsexp::from_slice(sexp).unwrap();
        let expr = Expression::of_sexp(&sexp).unwrap();
        assert!(matches!(expr, Expression::Base(uuid, sub) if uuid == "t" && sub.is_empty()));
    }

    #[test]
    fn test_top_app() {
        let sexp = r#"(Top_app
                 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ())"#;
        let expr = sexp.parse().unwrap();
        assert!(matches!(expr, Expression::Top_app(..)));
    }

    #[test]
    fn test_group() {
        let base = Expression::Base("base".to_string(), Vec::new());
        let member = ("t".to_string(), (Vec::new(), base));
        let group = super::Group {
            gid: 123,
            loc: "foo.ml".to_string(),
            members: vec![member],
        };
        println!("{}", group.sexp_of());
    }

    #[test]
    fn test_poly_constr() {
        let sexp = r#"(Constr
                                            (One
                                             ((Var
                                               (src/lib/one_or_two/one_or_two.ml:7:26
                                                a)))))"#;
        let expr = sexp.parse().unwrap();
        assert!(matches!(expr, PolyConstr::Constr(..)));
    }
}
