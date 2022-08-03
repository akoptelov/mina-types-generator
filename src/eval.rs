use std::collections::HashMap;

use thiserror::Error;
use crate::select::{ValueMutSelector, SelectingMutWithValue};

use super::shape::*;

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
