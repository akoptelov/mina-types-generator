use std::collections::HashMap;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};

use crate::xref::XRef;

use super::shape::*;

pub struct Generator<'a> {
    xref: &'a XRef<'a>,
    venv: HashMap<&'a str, TokenStream>,
    defs: Vec<TokenStream>,
}

macro_rules! gen_error {
    ($($arg:tt)*) => {{
        let res = std::fmt::format(format_args!($($arg)*));
        syn::Error::new(proc_macro2::Span::call_site(), res).to_compile_error()
    }}
}

macro_rules! gen_bail {
    ($($arg:tt)*) => {{
        return gen_error!($($arg)*);
    }}
}

impl<'a> Generator<'a> {
    pub fn new(xref: &'a XRef<'a>) -> Self {
        Self {
            xref,
            venv: HashMap::new(),
            defs: Vec::new(),
        }
    }

    pub fn generate(&'a mut self, name: &str) -> TokenStream {
        let ty = if let Some(ty) = self.xref.for_name(name) {
            ty
        } else {
            gen_bail!("name `{name}` not found");
        };

        let main = self.generate_expression(name, ty);
        let defs = self.defs.iter();

        quote! {
            #main
            #(
                #defs
            )*
        }
    }

    /// Generates type with specified `name` according to the shape `expr`.
    fn generate_expression(&mut self, name: &str, expr: &'a Expression) -> TokenStream {
        match expr {
            Expression::Annotate(_, _) => todo!(),
            Expression::Base(uuid, exprs) => self.base(name, uuid, exprs),
            Expression::Record(_) => todo!(),
            Expression::Variant(alts) => self.variant(name, alts),
            Expression::Tuple(_) => todo!(),
            Expression::Poly_variant(_) => todo!(),
            Expression::Var(_) => todo!(),
            Expression::Rec_app(_, _) => todo!(),
            Expression::Top_app(group, tid, args) => self.top_app(name, group, tid, args),
        }
    }

    /// Resolves type name for the shape `expr`, generating it if needed.
    fn resolve_expression(&mut self, _expr: &Expression) -> TokenStream {
        todo!()
    }

    fn top_app(
        &mut self,
        name: &str,
        group: &'a Group,
        tid: &Tid,
        args: &Vec<Expression>,
    ) -> TokenStream {
        let args = args
            .iter()
            .map(|arg| self.resolve_expression(arg))
            .collect();

        let group = self.group(name, group, tid, &args);
        quote! {
            #group
        }
    }

    /// Substitutes
    fn group(
        &mut self,
        name: &str,
        group: &'a Group,
        tid: &Tid,
        args: &Vec<TokenStream>,
    ) -> TokenStream {
        let Group {
            gid: _,
            loc,
            members,
        } = group;
        let docstr = format!("Location: {loc}");
        if members.len() != 1 {
            gen_bail!("too many members in group for {name}");
        }
        if &members[0].0 != tid {
            gen_bail!(
                "group item name `{gtid}` differs from expected `{tid}`",
                gtid = members[0].0
            );
        }
        let members = members
            .iter()
            .map(|(tid, (vids, expr))| self.member(name, tid, vids, args, expr));
        quote! {
            #![doc = #docstr]
            #(
                #members
            )*
        }
    }

    fn member(
        &mut self,
        name: &str,
        _tid: &Tid,
        vids: &'a Vec<Vid>,
        args: &Vec<TokenStream>,
        expr: &'a Expression,
    ) -> TokenStream {
        if vids.len() != args.len() {
            gen_bail!(
                "vids lenght `{}` differs from args len `{}` for {}",
                vids.len(),
                args.len(),
                name
            );
        }
        let mut venv =
            vids.iter()
                .zip(args.iter())
                .fold(self.venv.clone(), |mut venv, (vid, arg)| {
                    venv.insert(vid.as_str(), arg.clone());
                    venv
                });
        std::mem::swap(&mut venv, &mut self.venv);
        let res = self.generate_expression(name, expr);
        std::mem::swap(&mut venv, &mut self.venv);
        res
    }

    fn expression(&mut self, expr: &Expression) -> TokenStream {
        match expr {
            Expression::Base(uuid, _expr) => {
                let name = format_ident!("{uuid}");
                quote!(#name)
            }
            Expression::Variant(alts) => {
                let name = "VariantName";
                let def = self.variant(name, alts);
                self.defs.push(def);
                let name = format_ident!("{name}");
                quote!(#name)
            }
            Expression::Var((_loc, vid)) => {
                if let Some(arg) = self.venv.get(vid.as_str()) {
                    arg.clone()
                } else {
                    gen_error!("No expansion for type variable `{vid}`")
                }
            }
            _ => todo!(),
        }
    }

    fn base(&mut self, name: &str, uuid: &str, _exprs: &Vec<Expression>) -> TokenStream {
        let name = format_ident!("{name}");
        let uuid = format_ident!("{uuid}");
        quote! {
            pub type #name = #uuid;
        }
    }

    fn variant(&mut self, name: &str, alts: &Vec<(String, Vec<Expression>)>) -> TokenStream {
        let name = format_ident!("{name}");
        let alts = alts
            .iter()
            .map(|(name, fields)| self.alternative(name, fields));
        quote! {
            pub enum #name {
                #(#alts),*
            }
        }
    }

    fn alternative(&mut self, name: &str, fields: &Vec<Expression>) -> TokenStream {
        let name = format_ident!("{name}");
        if fields.is_empty() {
            quote!(#name)
        } else {
            let fields = fields.iter().map(|field| self.expression(field));
            quote! {
                #name(#(#fields),*)
            }
        }
    }
}

#[cfg(test)]
mod tests {

    use rsexp::OfSexp;

    use super::*;

    fn format_tokens(ts: TokenStream) -> String {
        use rust_format::{Formatter, RustFmt};
        RustFmt::default().format_tokens(ts.into()).unwrap()
    }

    fn from_sexp(sexp: &str) -> Expression {
        <Expression as OfSexp>::of_sexp(&rsexp::from_slice(sexp).unwrap()).unwrap()
    }

    #[test]
    fn gen_unsigned() {
        let expr = from_sexp(
            r#"
(Top_app
 ((gid 125) (loc src/int64.ml:6:6) (members ((t (() (Base int64 ())))))) t
 ())
"#,
        );

        let types = vec![("my_int", expr)];
        let xref = XRef::new(&types).unwrap();
        let mut gen = Generator::new(&xref);

        let ts = gen.generate("my_int");
        println!("{}", format_tokens(ts));
    }

    #[test]
    fn gen_variant() {
        let expr = from_sexp(
            r#"(Top_app
 ((gid 551) (loc src/lib/sgn/sgn.ml:9:4)
  (members ((t (() (Variant ((Pos ()) (Neg ()))))))))
 t ())"#,
        );
        let types = vec![("my_variant", expr)];
        let xref = XRef::new(&types).unwrap();
        let mut gen = Generator::new(&xref);

        let ts = gen.generate("my_variant");
        println!("{}", format_tokens(ts));
    }

    #[test]
    fn gen_var_app() {
        let member = (
            "t".to_string(),
            (
                Vec::new(),
                Expression::Variant(vec![
                    ("Pos".to_string(), vec![]),
                    ("Neg".to_string(), vec![]),
                ]),
            ),
        );
        let expr = Expression::Top_app(
            Group {
                gid: 119,
                loc: "src/lib/sgn/sgn.ml:9:4".to_string(),
                members: vec![member],
            },
            "t".to_string(),
            Vec::new(),
        );

        let types = vec![("my_variant", expr)];
        let xref = XRef::new(&types).unwrap();
        let mut gen = Generator::new(&xref);

        let ts = gen.generate("my_variant");
        println!("{}", format_tokens(ts));
    }
}
