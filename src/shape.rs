use std::{collections::HashMap, str::FromStr};

use derive_new::new;
use rsexp::OfSexp;
use rsexp_derive::{OfSexp, SexpOf};
use thiserror::Error;

use crate::select::{SelectingMutWithValue, ValueMutSelector};

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

#[derive(Debug, Error)]
pub enum CanonicalizeError {
    #[error("Empty group `{0}`")]
    EmptyGroup(Gid),
    #[error("Unknown type variable {0}")]
    UnknownVar(Vid),
    #[error("Different lenght of type parameters `{1}` and arguments `{2}` for group `{0}`")]
    TypeParametersLenght(Gid, usize, usize),
}

pub fn eval(expr: &Expression) -> Result<Expression, CanonicalizeError> {
    Canonicalize {
        venv: HashMap::new(),
    }
    .process(expr)
}

struct Canonicalize {
    venv: HashMap<Vid, Expression>,
}

impl Canonicalize {
    fn process(&mut self, expr: &Expression) -> Result<Expression, CanonicalizeError> {
        expr.select_mut_with_value(self)
    }

    fn collect<T, I>(iter: I) -> Result<Vec<T>, CanonicalizeError>
    where
        I: Iterator<Item = Result<T, CanonicalizeError>>,
    {
        iter.collect()
    }

    fn group(
        &mut self,
        gid: &Gid,
        loc: &Location,
        members: &Vec<(Tid, (Vec<Vid>, Expression))>,
        args: &Vec<Expression>,
    ) -> Result<Group, CanonicalizeError> {
        let (tid, (vids, expr)) = members
            .first()
            .ok_or_else(|| CanonicalizeError::EmptyGroup(*gid))?;

        let venv = self.new_venv(gid, vids, args)?;
        let expr = self.process(expr);
        self.restore_venv(venv);
        let mut expr = expr?;

        if let Expression::Top_app(group, _, _) = expr {
            let (_, (_, inner)) = group
                .members
                .into_iter()
                .next()
                .ok_or_else(|| CanonicalizeError::EmptyGroup(group.gid))?;
            expr = inner;
        }

        Ok(Group {
            gid: *gid,
            loc: loc.clone(),
            members: vec![(tid.clone(), (vec![], expr))],
        })
    }

    fn poly_constr(&mut self, constr: &PolyConstr) -> Result<PolyConstr, CanonicalizeError> {
        Ok(match constr {
            PolyConstr::Constr((loc, opt_expr)) => PolyConstr::Constr((
                loc.clone(),
                opt_expr
                    .as_ref()
                    .map(|expr| Ok(Box::new(self.process(expr.as_ref())?)))
                    .transpose()?,
            )),
            PolyConstr::Inherit((loc, expr)) => {
                PolyConstr::Inherit((loc.clone(), Box::new(self.process(expr)?)))
            }
        })
    }

    fn new_venv(
        &mut self,
        gid: &Gid,
        vids: &Vec<Vid>,
        args: &Vec<Expression>,
    ) -> Result<HashMap<Vid, Expression>, CanonicalizeError> {
        if vids.len() != args.len() {
            return Err(CanonicalizeError::TypeParametersLenght(
                *gid,
                vids.len(),
                args.len(),
            ));
        }

        let venv = vids
            .iter()
            .zip(args.iter())
            .fold(self.venv.clone(), |mut venv, (vid, expr)| {
                venv.insert(vid.clone(), expr.clone());
                venv
            });
        Ok(std::mem::replace(&mut self.venv, venv))
    }

    fn restore_venv(&mut self, venv: HashMap<Vid, Expression>) {
        self.venv = venv;
    }
}

impl ValueMutSelector<Result<Expression, CanonicalizeError>> for Canonicalize {
    fn default_result(&mut self) -> Result<Expression, CanonicalizeError> {
        unreachable!("should not be called")
    }

    fn annotate(
        &mut self,
        uuid: &Uuid,
        expr: &Expression,
    ) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Annotate(
            uuid.clone(),
            Box::new(self.process(expr)?),
        ))
    }

    fn base(
        &mut self,
        uuid: &Uuid,
        exprs: &Vec<Expression>,
    ) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Base(
            uuid.clone(),
            Self::collect(exprs.iter().map(|expr| self.process(expr)))?,
        ))
    }

    fn record(
        &mut self,
        fields: &Vec<(String, Expression)>,
    ) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Record(Self::collect(fields.iter().map(
            |(name, expr)| Ok((name.clone(), self.process(expr)?)),
        ))?))
    }

    fn variant(
        &mut self,
        alts: &Vec<(String, Vec<Expression>)>,
    ) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Variant(Self::collect(alts.iter().map(
            |(name, exprs)| {
                Ok((
                    name.clone(),
                    Self::collect(exprs.iter().map(|expr| self.process(expr)))?,
                ))
            },
        ))?))
    }

    fn tuple(&mut self, elems: &Vec<Expression>) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Tuple(Self::collect(
            elems.iter().map(|expr| self.process(expr)),
        )?))
    }

    fn poly_variant(
        &mut self,
        loc: &Location,
        constrs: &Vec<PolyConstr>,
    ) -> Result<Expression, CanonicalizeError> {
        let constrs = Self::collect(constrs.iter().map(|constr| self.poly_constr(constr)))?;
        Ok(Expression::Poly_variant((loc.clone(), constrs)))
    }

    fn var(&mut self, _loc: &Location, vid: &Vid) -> Result<Expression, CanonicalizeError> {
        self.venv
            .get(vid)
            .cloned()
            .ok_or_else(|| CanonicalizeError::UnknownVar(vid.clone()))
    }

    fn rec_app(
        &mut self,
        tid: &Tid,
        _args: &Vec<Expression>,
    ) -> Result<Expression, CanonicalizeError> {
        Ok(Expression::Rec_app(tid.clone(), vec![]))
    }

    fn top_app(
        &mut self,
        group: &Group,
        tid: &Tid,
        args: &Vec<Expression>,
    ) -> Result<Expression, CanonicalizeError> {
        let args = Self::collect(args.iter().map(|expr| self.process(expr)))?;
        let Group { gid, loc, members } = group;
        let group = self.group(gid, loc, members, &args)?;
        Ok(Expression::Top_app(group, tid.clone(), vec![]))
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
