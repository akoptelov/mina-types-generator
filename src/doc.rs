use std::{collections::HashSet, io::Write};

use thiserror::Error;

use crate::{
    select::{SelectingMutWithValue, SelectingWithValue, ValueMutSelector, ValueSelector},
    shape::{Expression, Gid, Group, Tid, Vid},
    visit::{ValueMutVisiting, ValueMutVisitor},
    xref::XRef,
};

///! Module defining documentation functionality for bin_prot shapes

#[derive(Debug, Error)]
pub enum Error {
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error("Empty group `{0}`")]
    EmptyGroup(Gid),
    #[error("Different lenght of type parameters `{1}` and arguments `{2}` for group `{0}`")]
    MismatchTypeParametersLenght(Gid, usize, usize),
    #[error("Type `{0}` not found")]
    TypeNotFound(String),
}

pub struct Doc<'a, O>
where
    O: Write,
{
    xref: &'a XRef<'a>,
    out: &'a mut O,
    git_base: String,
    all: bool,
    done: HashSet<Gid>,
}

pub type Result<T = ()> = std::result::Result<T, Error>;

fn reduce(a: Result<()>, v: Result<()>) -> Result<()> {
    a.or(v)
}

impl<'a, O> Doc<'a, O>
where
    O: Write,
{
    pub fn new(xref: &'a XRef<'a>, git_base: String, out: &'a mut O) -> Self {
        Self {
            xref,
            git_base,
            out,
            all: false,
            done: HashSet::new(),
        }
    }

    pub fn generate(&'a mut self, name: &str) -> Result {
        let group = self
            .xref
            .for_name(name)
            .ok_or_else(|| Error::TypeNotFound(name.to_string()))?;
        self.generate_group(group)
    }

    pub fn generate_all(&'a mut self) -> Result<()> {
        self.all = true;
        self.xref
            .named()
            .try_for_each(|(_name, group)| self.generate_group(group))
    }

    /// Generates group's member(s)
    fn generate_group(&mut self, group: &'a Group) -> Result<()> {
        let (_, (vids, expr)) = group_first_expr(group)?;

        self.print_type_header(group)?;
        self.print_type_parameters(vids)?;
        self.print_type_structure(expr)?;

        group
            .visit_mut_with_value(self, &reduce)
            .unwrap_or(Ok(()))?;

        Ok(())
    }

    fn print_type_header(&mut self, group: &Group) -> Result {
        let name = self.xref.get_group_name(group.gid);
        writeln!(
            self.out,
            "\n\n### Type `{name}`\n[{loc}]({base}{git_loc})\n",
            loc = group.loc,
            base = self.git_base,
            git_loc = loc_to_git(&group.loc).unwrap_or_else(|| group.loc.clone()),
        )?;

        Ok(())
    }

    fn print_type_parameters(&mut self, vids: &Vec<Vid>) -> Result {
        if !vids.is_empty() {
            writeln!(self.out, "\n**Type parameters**:",)?;
            vids.iter()
                .map(|vid| Ok(writeln!(self.out, "- `{vid}`")?))
                .collect::<Result<()>>()?;
        }

        Ok(())
    }

    fn print_type_structure(&mut self, expr: &Expression) -> Result {
        ExpressionDoc::generate(expr, self.xref, self.out)?;
        Ok(())
    }

    fn named_group(&self, gid: Gid) -> bool {
        self.xref
            .for_gid(gid)
            .map_or(false, |(_, name)| name.is_some())
    }

    fn unnamed_group_for_external_type(&self, group: &Group) -> Result<bool> {
        Ok(matches!(
            group
                .members
                .first()
                .ok_or_else(|| Error::EmptyGroup(group.gid))?
                .1
                 .1,
            Expression::Base(_, _)
        ) && self.xref.for_gid(group.gid).is_none())
    }
}

impl<'a, O, F> ValueMutVisitor<'a, Result<()>, F> for Doc<'a, O>
where
    O: Write,
    F: Fn(Result<()>, Result<()>) -> Result<()>,
{
    fn apply(&mut self, expr: &'a Expression, f: &F) -> Result<()> {
        if let Expression::Top_app(group, _, exprs) = expr {
            if self.all && self.named_group(group.gid) {
                return Ok(());
            }
            if self.unnamed_group_for_external_type(&group)? {
                return Ok(());
            }
            if !self.done.insert(group.gid) {
                return Ok(());
            }
            self.generate_group(group)?;
            exprs.iter().try_for_each(|expr| self.apply(expr, f))?;
        } else {
            expr.visit_mut_with_value(self, f).unwrap_or(Ok(()))?;
        }

        Ok(())
    }
}

#[derive(Debug)]
enum ExpressionType {
    Named(String),
    Parameter(String),
    External(String, Vec<ExpressionType>),
    Tuple(Vec<ExpressionType>),
    Anonimous(Gid),
    Unknown(Expression),
}

impl ExpressionType {
    fn type_to_type_and_anchor(s: &str, anchor_prefix: &str) -> String {
        let mut anchor = String::new();
        for ch in s.chars() {
            if ch == '_' || ch == '-' || ch.is_numeric() {
                anchor.push(ch);
            } else if ch.is_alphabetic() {
                anchor.push(ch.to_ascii_lowercase());
            }
        }
        format!("[{s}](#{anchor_prefix}{anchor})")
    }

    fn as_md_reference(&self, anchor_prefix: &str) -> String {
        match self {
            ExpressionType::Named(s) => Self::type_to_type_and_anchor(s, anchor_prefix),
            ExpressionType::Parameter(s) => format!("parameter `{s}`"),
            ExpressionType::External(s, args) if !args.is_empty() => format!(
                "external type `{s}` of ({})",
                args.iter()
                    .map(|arg| arg.as_md_reference(anchor_prefix))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExpressionType::External(s, _) => format!("external type `{s}`"),
            ExpressionType::Tuple(list) => format!(
                "({})",
                list.iter()
                    .map(|t| t.as_md_reference(anchor_prefix))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            ExpressionType::Anonimous(gid) => format!("anonymous-{gid}"),
            ExpressionType::Unknown(expr) => format!("<cannot resolve type: {expr:?}>"),
        }
    }
}

trait ReferenceResolver {
    fn get_group_name(&self, gid: Gid) -> String;
    fn resolve_group_name(&self, gid: Gid) -> ExpressionType;
    fn resolve_exression_type(&self, expr: &Expression) -> ExpressionType;
}

impl<'a> ReferenceResolver for XRef<'a> {
    fn get_group_name(&self, gid: Gid) -> String {
        self.for_gid(gid)
            .and_then(|(_, name)| name)
            .map_or_else(|| format!("anonymous-{gid}"), String::from)
    }

    fn resolve_group_name(&self, gid: Gid) -> ExpressionType {
        self.for_gid(gid)
            .and_then(|(group, name)| {
                name.map(String::from)
                    .map(ExpressionType::Named)
                    .or_else(|| {
                        group.members.first().and_then(|(_, (_, expr))| {
                            if let Expression::Base(uuid, exprs) = expr {
                                self.base(uuid, exprs)
                            } else {
                                None
                            }
                        })
                    })
            })
            .unwrap_or_else(|| ExpressionType::Anonimous(gid))
    }

    fn resolve_exression_type(&self, expr: &Expression) -> ExpressionType {
        expr.select_with_value(self)
            .unwrap_or_else(|| ExpressionType::Unknown(expr.clone()))
    }
}

impl<'a> ValueSelector<Option<ExpressionType>> for XRef<'a> {
    fn default_result(&self) -> Option<ExpressionType> {
        None
    }

    fn base(&self, uuid: &crate::shape::Uuid, exprs: &Vec<Expression>) -> Option<ExpressionType> {
        Some(ExpressionType::External(
            uuid.to_string(),
            exprs
                .iter()
                .map(|expr| self.resolve_exression_type(expr))
                .collect(),
        ))
    }

    fn tuple(&self, elems: &Vec<Expression>) -> Option<ExpressionType> {
        Some(ExpressionType::Tuple(
            elems
                .iter()
                .map(|expr| self.resolve_exression_type(expr))
                .collect(),
        ))
    }

    fn var(&self, _loc: &crate::shape::Location, vid: &Vid) -> Option<ExpressionType> {
        Some(ExpressionType::Parameter(vid.to_string()))
    }

    fn top_app(
        &self,
        group: &Group,
        _tid: &crate::shape::Tid,
        _args: &Vec<Expression>,
    ) -> Option<ExpressionType> {
        Some(self.resolve_group_name(group.gid))
    }
}

struct ExpressionDoc<'a, O> {
    xref: &'a XRef<'a>,
    out: &'a mut O,
}

impl<'a, O> ExpressionDoc<'a, O>
where
    O: Write,
{
    fn generate(expr: &'a Expression, xref: &'a XRef<'a>, out: &'a mut O) -> Result<()> {
        let mut s = Self { xref, out };
        expr.select_mut_with_value(&mut s)?;
        Ok(())
    }

    fn print_kind(&mut self, kind: String) -> Result {
        writeln!(self.out, "\n**Kind:** {kind}")?;
        Ok(())
    }
}

fn group_first_expr(group: &Group) -> Result<&(Tid, (Vec<Vid>, Expression))> {
    group
        .members
        .first()
        .ok_or_else(|| Error::EmptyGroup(group.gid))
}

impl<'a, O> ValueMutSelector<Result<()>> for ExpressionDoc<'a, O>
where
    O: Write,
{
    fn top_app(
        &mut self,
        group: &Group,
        _tid: &crate::shape::Tid,
        args: &Vec<Expression>,
    ) -> Result<()> {
        let base = self.xref.get_group_name(group.gid);
        let base = ExpressionType::type_to_type_and_anchor(&base, "type-");
        self.print_kind(format!("Instance of {base}"))?;
        if !args.is_empty() {
            writeln!(self.out, r#"**Type Arguments:**"#)?;
            let vids = &group_first_expr(group)?.1 .0;
            if args.len() != vids.len() {
                return Err(Error::MismatchTypeParametersLenght(
                    group.gid,
                    vids.len(),
                    args.len(),
                ));
            }
            for (arg, param) in args.iter().zip(vids.iter()) {
                let arg = self
                    .xref
                    .resolve_exression_type(arg)
                    .as_md_reference("type-");
                writeln!(self.out, "- {arg} as `{param}`")?;
            }
        }
        Ok(())
    }

    fn record(&mut self, fields: &Vec<(String, Expression)>) -> Result<()> {
        self.print_kind("Record".to_string())?;
        for (name, ty) in fields {
            let ty = self
                .xref
                .resolve_exression_type(ty)
                .as_md_reference("type-");
            writeln!(self.out, "- `{name}`: {ty}")?
        }
        Ok(())
    }

    fn variant(&mut self, alts: &Vec<(String, Vec<Expression>)>) -> Result<()> {
        self.print_kind("Variant".to_string())?;
        for (name, exprs) in alts {
            writeln!(self.out, "- `{name}`:")?;
            for expr in exprs {
                let ty = self
                    .xref
                    .resolve_exression_type(expr)
                    .as_md_reference("type-");
                writeln!(self.out, "  - {ty}")?;
            }
        }
        Ok(())
    }

    fn tuple(&mut self, elems: &Vec<Expression>) -> Result<()> {
        self.print_kind("Tuple".to_string())?;
        for ty in elems {
            let ty = self
                .xref
                .resolve_exression_type(ty)
                .as_md_reference("type-");
            writeln!(self.out, "- {ty}")?
        }
        Ok(())
    }

    fn base(&mut self, uuid: &crate::shape::Uuid, exprs: &Vec<Expression>) -> Result<()> {
        let type_expr = ExpressionType::External(
            uuid.clone(),
            exprs
                .iter()
                .map(|expr| self.xref.resolve_exression_type(expr))
                .collect(),
        );
        writeln!(
            self.out,
            "Alias of `{}`",
            type_expr.as_md_reference("type-")
        )?;
        Ok(())
    }

    fn default_result(&mut self) -> Result<()> {
        writeln!(self.out, "Not implemented")?;
        Ok(())
    }
}

fn loc_to_git(loc: &str) -> Option<String> {
    let mut split = loc.split(':');
    let file = split.next()?;
    let line = split.next()?;
    Some(format!("{file}#L{line}"))
}

#[cfg(test)]
mod tests {
    use crate::{shape::eval, xref::XRef};

    use super::Doc;

    #[test]
    fn gen_doc() {
        let sexp = r#"(Top_app
 ((gid 728) (loc src/lib/mina_base/zkapp_statement.ml:28:4)
  (members
   ((t
     (()
      (Top_app
       ((gid 727) (loc src/lib/mina_base/zkapp_statement.ml:15:6)
        (members
         ((t
           ((comm)
            (Record
             ((party (Var (src/lib/mina_base/zkapp_statement.ml:15:31 comm)))
              (calls (Var (src/lib/mina_base/zkapp_statement.ml:15:46 comm))))))))))
       t ((Base kimchi_backend_bigint_32_V1 ()))))))))
 t ())"#;

        let expr = sexp.parse().unwrap();
        let expr = eval(&expr).unwrap();
        let exprs = vec![("my_type", expr)];
        let xref = XRef::new(&exprs).unwrap();
        let mut out = Vec::new();
        let git_base =
            "https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/";
        let mut doc = Doc::new(&xref, git_base.to_string(), &mut out);
        doc.generate_all().unwrap();
        println!("{}", String::from_utf8(out).unwrap());
    }
}
