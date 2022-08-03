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

#[derive(Debug, Clone, PartialEq, Eq, OfSexp, SexpOf, new)]
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

#[derive(Debug, Clone, PartialEq, Eq, OfSexp, SexpOf)]
pub struct Group {
    pub gid: Gid,
    pub loc: Location,
    pub members: Vec<(Tid, (Vec<Vid>, Expression))>,
}

#[derive(Debug, Clone, PartialEq, Eq, OfSexp, SexpOf)]
pub enum PolyConstr {
    Constr((String, Option<Box<Expression>>)),
    Inherit((Location, Box<Expression>)),
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

impl Expression {
    pub fn as_group(&self) -> Option<&Group> {
        if let Expression::Top_app(group, ..) = self {
            Some(group)
        } else {
            None
        }
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
