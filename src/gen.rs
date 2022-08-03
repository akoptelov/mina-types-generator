use std::{collections::HashMap, io::Write, ops::Deref};

use derive_builder::Builder;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use rust_format::{Config, Formatter, PostProcess, RustFmt};
use thiserror::Error;

use crate::xref::XRef;

use super::shape::*;

type Venv<'a> = HashMap<&'a str, TokenStream>;
type Tenv<'a> = HashMap<&'a str, TokenStream>;

macro_rules! gen_error {
    ($($arg:tt)*) => {{
        let res = std::fmt::format(format_args!($($arg)*));
        syn::Error::new(proc_macro2::Span::call_site(), res).to_compile_error()
    }}
}

#[derive(Debug, Error)]
pub enum Error<'a> {
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error("Empty group `{0}`")]
    EmptyGroup(&'a Gid),
    #[error("Different lenght of type parameters `{1}` and arguments `{2}` for group `{0}`")]
    MismatchTypeParametersLenght(&'a Gid, usize, usize),
    #[error("Type `{0}` not found")]
    TypeNotFound(String),
}

impl<'a> From<Error<'a>> for TokenStream {
    fn from(source: Error<'a>) -> Self {
        gen_error!("{source}")
    }
}

#[derive(Clone, Copy, Default, PartialEq, Eq)]
enum Context<'a> {
    #[default]
    Root,
    TopApp,
    TypeArg(usize),
    RecordField(&'a str),
    VariantAlt(&'a str, usize),
    TupleItem(usize),
}

#[derive(Builder)]
#[builder(setter(skip))]
pub struct Generator<'a> {
    /// Type expression name/id information.
    #[builder(setter(skip = false))]
    xref: &'a XRef<'a>,
    /// Type variables substitution.
    venv: Venv<'a>,
    /// Types substitution (for recursive types).
    tenv: Tenv<'a>,
    /// Current type name.
    current_name: Option<String>,
    /// Current context.
    context: Context<'a>,
    /// Base types mapping.
    #[builder(default = "base_types()")]
    base_types: HashMap<String, BaseTypeMapping>,
    /// Generated groups.
    generated: HashMap<&'a Gid, String>,
    /// Generate comments.
    #[builder(setter(skip = false), default)]
    generate_comments: bool,
    /// Git repository prefix
    #[builder(setter(into, strip_option), default)]
    git_prefix: Option<String>,
}

pub type Result<'a, T = ()> = std::result::Result<T, Error<'a>>;

enum BaseTypeArgs {
    None,
    Single,
}

struct BaseTypeMapping {
    rust_id: Option<String>,
    args_num: BaseTypeArgs,
}

impl BaseTypeMapping {
    fn rust_id(&self) -> Option<&str> {
        self.rust_id.as_ref().map(|s| s.as_str())
    }
}

impl<'a> Generator<'a> {
    fn new(xref: &'a XRef<'a>) -> Self {
        Self {
            xref,
            venv: HashMap::new(),
            tenv: HashMap::new(),
            current_name: None,
            context: Context::Root,
            base_types: base_types(),
            generated: HashMap::new(),
            generate_comments: false,
            git_prefix: Some("git/".to_string()),
        }
    }

    pub fn generate_types<T, I, O>(&mut self, types: I, out: &mut O) -> Result<'a, ()>
    where
        T: 'a + AsRef<str>,
        I: IntoIterator<Item = T>,
        O: Write,
    {
        for ty in types {
            let ty = ty.as_ref();
            let ts = self.generate(ty)?;
            let config = Config::new_str().post_proc(PostProcess::ReplaceMarkersAndDocBlocks);
            let res = RustFmt::from_config(config)
                .format_tokens(ts.into())
                .unwrap();
            out.write_all(res.as_bytes())?;
            // out.write_all(
            //     ts.to_string().as_bytes(), // res
            // )?;
            //
        }
        Ok(())
    }

    fn generate(&mut self, name: &str) -> Result<'a, TokenStream> {
        let expr = self
            .xref
            .expr_for_name(name)
            .ok_or_else(|| Error::TypeNotFound(name.to_string()))?;
        Ok(self.generate_type(expr))
    }

    fn generate_type(&mut self, expr: &'a Expression) -> TokenStream {
        match expr {
            Expression::Annotate(_, _) => todo!(),
            Expression::Base(uuid, args) => self.generate_base_type(uuid, args),
            Expression::Record(exprs) => self.generate_record(exprs),
            Expression::Variant(alts) => self.generate_variant(alts),
            Expression::Tuple(exprs) => self.generate_tuple(exprs),
            Expression::Poly_variant(_) => todo!(),
            Expression::Var((loc, vid)) => self.generate_var(loc, vid),
            Expression::Rec_app(tid, args) => self.generate_rec_app(tid, args),
            Expression::Top_app(group, tid, args) => self.generate_top_app(group, tid, args),
        }
    }

    fn generate_base_type(&mut self, uuid: &str, args: &'a [Expression]) -> TokenStream {
        let args = args
            .iter()
            .map(|arg| self.type_reference(arg))
            .collect::<Vec<_>>();
        let base = self.base_type_mapping(uuid, &args);
        let name = self.current_name_tokens();
        quote!(pub type #name = #base;)
    }

    fn generate_record(&mut self, fields: &'a [(String, Expression)]) -> TokenStream {
        let name = self.current_name_tokens();
        let old_context = self.context.clone();
        let field_types = fields.iter().map(|(field, expr)| {
            if self.xref.can_inline_expression(expr) {
                return quote!();
            }
            self.context = Context::RecordField(field);
            self.generate_type(expr)
        });
        let field_types = quote!(#(#field_types)*);
        self.context = old_context;

        let fields = fields
            .iter()
            .map(|(name, expr)| self.generate_field(name, expr));
        quote! {
            pub struct #name {
                #(#fields,)*
            }

            #field_types
        }
    }

    fn generate_field(&mut self, name: &str, expr: &'a Expression) -> TokenStream {
        let field_name = format_ident!("{}", name);
        let field_type = self.type_reference(expr);
        quote! {
            pub #field_name: #field_type
        }
    }

    fn generate_variant(&mut self, alts: &'a [(String, Vec<Expression>)]) -> TokenStream {
        let name = self.current_name_tokens();
        let alts = alts
            .iter()
            .map(|(alt, exprs)| self.generate_alternative(alt, exprs));
        quote! {
            pub enum #name {
                #(
                    #alts,
                )*
            }
        }
    }

    fn generate_alternative(&mut self, alt: &str, exprs: &'a [Expression]) -> TokenStream {
        let alt_name = format_ident!("{}", alt);
        if exprs.is_empty() {
            quote!(#alt_name)
        } else {
            let exprs = exprs.iter().map(|expr| self.type_reference(expr));
            quote!(#alt_name(#(#exprs,)*))
        }
    }

    fn generate_tuple(&mut self, exprs: &'a [Expression]) -> TokenStream {
        let name = self.current_name_tokens();
        let exprs = exprs.iter().map(|expr| self.type_reference(expr));
        quote! {
            pub type #name = (#(#exprs,)*);
        }
    }

    fn generate_var(&mut self, _loc: &str, _vid: &str) -> TokenStream {
        quote!()
    }

    fn generate_rec_app(&mut self, _tid: &str, _args: &[Expression]) -> TokenStream {
        todo!()
    }

    fn generate_top_app(
        &mut self,
        group: &'a Group,
        _tid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        if self.xref.is_anonymous(group.gid) && self.generated.contains_key(&group.gid) {
            return quote!();
        }

        let arg_types = args
            .iter()
            // .filter(|arg| !self.xref.can_inline_expression(arg))
            .enumerate()
            .map(|(i, arg)| {
                let context = std::mem::replace(&mut self.context, Context::TypeArg(i));
                let res = self.generate_type(arg);
                self.context = context;
                res
            })
            .collect::<Vec<_>>();

        let main = self
            .generate_top_app_group(group, args)
            .unwrap_or_else(|e| e.into());

        quote! {
            #main
            #(#arg_types)*
        }
    }

    fn git_loc(&self, loc: &str) -> Option<String> {
        let prefix = self.git_prefix.as_ref()?;
        let mut it = loc.split(':');
        let file = it.next()?;
        let line = it.next()?;
        Some(format!("[{loc}]({prefix}{file}#L{line})",))
    }

    fn generate_doc_comment(&self, gid: &Gid, loc: &str) -> TokenStream {
        let git_loc = self.git_loc(loc);
        let loc = git_loc.as_ref().map(String::as_str).unwrap_or(loc);
        let name = self
            .xref
            .for_gid(*gid)
            .and_then(|(_, name)| name)
            .map_or_else(|| format!("gid {gid}"), String::from);
        let doc = format!(" {name}\n {loc}");
        quote! {
            #[doc = #doc]
        }
    }

    fn generate_top_app_group(
        &mut self,
        group: &'a Group,
        args: &'a [Expression],
    ) -> Result<'a, TokenStream> {
        let Group { gid, loc, members } = group;
        // if self.generated.contains_key(&gid) {
        //     return Ok(quote!());
        // }
        //
        if self.xref.is_anonymous(*gid) && matches!(self.context, Context::TypeArg(_)) {
            return Ok(quote!());
        }
        let (tid, (vids, expr)) = first_member(gid, members)?;

        let (name, comment) = if matches!(self.context, Context::TopApp) {
            // for Top_app inside Top_app the name is reused.
            (None, None)
        } else {
            (
                Some(self.new_name(gid)),
                if self.generate_comments {
                    Some(self.generate_doc_comment(gid, loc))
                } else {
                    None
                },
            )
        };
        let context = std::mem::replace(&mut self.context, Context::TopApp);
        let venv = self.new_venv(&group.gid, vids, args)?;
        let tenv = self.new_tenv(gid, tid);

        let res = self.generate_type(expr);

        self.tenv = tenv;
        self.venv = venv;
        self.context = context;
        if let Some(name) = name {
            self.current_name = name;
        }

        Ok(quote! {
            #comment
            #res
        })
    }

    fn type_reference(&mut self, expr: &'a Expression) -> TokenStream {
        match expr {
            Expression::Annotate(uuid, expr) => self.type_reference_annotation(uuid, expr),
            Expression::Base(uuid, args) => self.type_reference_base(uuid, args),
            Expression::Record(fields) => self.type_reference_record(fields),
            Expression::Variant(alts) => self.type_reference_variant(alts),
            Expression::Tuple(exprs) => self.type_reference_tuple(exprs),
            Expression::Poly_variant((loc, consts)) => {
                self.type_reference_poly_variant(loc, consts)
            }
            Expression::Var((loc, vid)) => self.type_reference_var(loc, vid),
            Expression::Rec_app(tid, args) => self.type_reference_rec_app(tid, args),
            Expression::Top_app(group, tid, args) => self.type_reference_top_app(group, tid, args),
        }
    }

    fn type_reference_annotation(&self, _uuid: &str, _expr: &Expression) -> TokenStream {
        todo!()
    }

    fn type_reference_base(&mut self, uuid: &'a str, args: &'a [Expression]) -> TokenStream {
        let args = args
            .iter()
            .map(|arg| self.type_reference(arg))
            .collect::<Vec<_>>();
        self.base_type_mapping(uuid, &args)
    }

    fn type_reference_record(&self, _fields: &[(String, Expression)]) -> TokenStream {
        gen_error!("Cannot reference record")
    }

    fn type_reference_variant(&self, _alts: &[(String, Vec<Expression>)]) -> TokenStream {
        gen_error!("Cannot reference variant")
    }

    fn type_reference_tuple(&mut self, exprs: &'a [Expression]) -> TokenStream {
        let exprs = exprs.iter().map(|expr| self.type_reference(expr));
        quote!((#(#exprs),*))
    }

    fn type_reference_poly_variant(&mut self, _loc: &str, _constrs: &[PolyConstr]) -> TokenStream {
        todo!()
    }

    fn type_reference_var(&self, _loc: &str, vid: &str) -> TokenStream {
        self.venv
            .get(vid)
            .cloned()
            .unwrap_or_else(|| gen_error!("Type variable `{vid}` not found"))
    }

    fn type_reference_rec_app(&self, tid: &str, _args: &[Expression]) -> TokenStream {
        self.tenv
            .get(tid)
            .cloned()
            .unwrap_or_else(|| gen_error!("Type `{tid}` not found"))
    }

    fn type_reference_top_app(
        &mut self,
        group: &'a Group,
        _tid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        if self.xref.can_inline_group(group) {
            let (_tid, (vids, expr)) = if let Some(v) = group.members.first() {
                v
            } else {
                return gen_error!("Empty group `{}`", group.gid);
            };
            let venv = match self.new_venv(&group.gid, vids, args) {
                Ok(v) => v,
                Err(e) => return e.into(),
            };
            let res = self.type_reference(expr);
            self.venv = venv;
            res
        } else {
            let name = self.group_name_or_anon(&group.gid);
            format_ident!("{name}").to_token_stream()
        }
    }

    fn type_reference_group(&mut self, group: &'a Group) -> TokenStream {
        if self.xref.can_inline_group(group) {
            let (_tid, (_vids, expr)) = if let Some(v) = group.members.first() {
                v
            } else {
                return gen_error!("Empty group `{}`", group.gid);
            };
            self.type_reference(expr)
        } else {
            let name = self.group_name_or_anon(&group.gid);
            format_ident!("{name}").to_token_stream()
        }
    }

    fn new_name(&mut self, gid: &'a Gid) -> Option<String> {
        let new_name = self
            .group_name(gid)
            .map(|name| self.sanitize_name(name))
            .unwrap_or_else(|| {
                self.current_name.as_ref().map_or_else(
                    || format!("Anonymous{gid}"),
                    |name| match self.context {
                        Context::Root => name.to_string(),
                        Context::TopApp => name.to_string(),
                        Context::TypeArg(n) => format!("{name}Arg{n}"),
                        Context::RecordField(field) => format!("{name}Field{field}"),
                        Context::VariantAlt(alt, n) => format!("{name}Alt{alt}{n}"),
                        Context::TupleItem(n) => format!("{name}Item{n}"),
                    },
                )
            });
        self.generated.insert(gid, new_name.clone());
        std::mem::replace(&mut self.current_name, Some(new_name))
    }

    fn new_venv(
        &mut self,
        gid: &'a i32,
        vids: &'a [String],
        args: &'a [Expression],
    ) -> Result<'a, HashMap<&'a str, TokenStream>> {
        if vids.len() != args.len() {
            return Err(Error::MismatchTypeParametersLenght(
                gid,
                vids.len(),
                args.len(),
            ));
        }

        let other = args
            .iter()
            .map(|arg| self.type_reference(arg))
            .collect::<Vec<_>>();
        let venv =
            vids.iter()
                .zip(other.into_iter())
                .fold(self.venv.clone(), |mut venv, (vid, arg)| {
                    venv.insert(vid, arg);
                    venv
                });
        Ok(std::mem::replace(&mut self.venv, venv))
    }

    fn new_tenv(&mut self, _gid: &'a i32, tid: &'a str) -> HashMap<&'a str, TokenStream> {
        let mut tenv = self.tenv.clone();
        if let Some(name) = self.current_name.as_ref() {
            tenv.insert(tid, format_ident!("{name}").to_token_stream());
        }
        std::mem::replace(&mut self.tenv, tenv)
    }

    fn current_name_tokens(&self) -> TokenStream {
        self.current_name.as_ref().map_or_else(
            || gen_error!("Empty current name (shouldn't happen)"),
            |name| format_ident!("{name}").to_token_stream(),
        )
    }

    fn sanitize_name(&self, name: &str) -> String {
        let name = name.strip_suffix(".t").unwrap_or(name);
        let mut san_name = String::new();
        let mut to_upper = true;
        for ch in name.chars() {
            if ch.is_alphanumeric() {
                san_name.push(if to_upper {
                    ch.to_ascii_uppercase()
                } else {
                    ch
                });
                to_upper = false;
            } else {
                to_upper = true;
            }
        }
        san_name
    }

    /// Generates Rust representation of Ocaml type `uuid` with type arguments `args`.
    fn base_type_mapping(&self, uuid: &str, args: &[TokenStream]) -> TokenStream {
        if let Some(mapping) = self.base_types.get(uuid) {
            let name = format_ident!("{}", mapping.rust_id().unwrap_or(uuid));
            match (&mapping.args_num, args.len()) {
                (BaseTypeArgs::None, 0) => name.to_token_stream(),
                (BaseTypeArgs::Single, 1) => quote!(#name<#(#args),*>),
                _ => gen_error!("Unexpected number of aguments to base type {uuid}"),
            }
        } else {
            let name = format_ident!("{}", uuid);
            if args.is_empty() {
                quote!(#name)
            } else {
                quote!(#name<#(#args),*>)
            }
        }
    }

    fn group_name(&self, gid: &Gid) -> Option<&str> {
        self.xref
            .for_gid(*gid)
            .and_then(|(_, name)| name)
            .or_else(|| self.generated.get(gid).map(Deref::deref))
    }

    fn group_name_or_anon(&self, gid: &Gid) -> String {
        self.group_name(gid).map_or_else(
            || format!("Anonymous{gid}"),
            |name| self.sanitize_name(name),
        )
    }
}

fn first_member<'a>(
    gid: &'a Gid,
    members: &'a Vec<(Tid, (Vec<Vid>, Expression))>,
) -> Result<'a, &'a (Tid, (Vec<Vid>, Expression))> {
    members.first().ok_or_else(|| Error::EmptyGroup(gid))
}

macro_rules! t {
    ($name:ident) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping {
                rust_id: None,
                args_num: BaseTypeArgs::None,
            },
        )
    };
    ($name:ident => $rust_name:ident) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping {
                rust_id: Some(String::from(stringify!($rust_name))),
                args_num: BaseTypeArgs::None,
            },
        )
    };
    ($name:ident => $rust_name:ident < _ >) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping {
                rust_id: Some(String::from(stringify!($rust_name))),
                args_num: BaseTypeArgs::Single,
            },
        )
    };
}

fn base_types() -> HashMap<String, BaseTypeMapping> {
    HashMap::from([
        t!(bool),
        t!(int => i32),
        t!(int32 => i32),
        t!(float => f32),
        t!(string => String),
        t!(option => Option<_>),
        t!(array => Vec<_>),
        t!(list => Vec<_>),
    ])
}

#[cfg(test)]
mod tests {
    use proc_macro2::TokenStream;

    fn to_string(ts: TokenStream) -> String {
        use rust_format::{Formatter, RustFmt};
        RustFmt::default().format_tokens(ts.into()).unwrap()
    }

    mod type_ref {
        use crate::{gen::Generator, shape::Expression, xref::XRef};

        fn gen_ref(expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding: [(String, Expression); 0] = [];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(&xref).type_reference(&expr);
            ts.to_string()
        }

        fn gen_ref_top(name: &str, expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding = [(name, expr.clone())];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(&xref).type_reference(&expr);
            ts.to_string()
        }

        #[test]
        fn base_type_builtins() {
            assert_eq!(gen_ref("(Base bool ())"), "bool");
            assert_eq!(gen_ref("(Base string ())"), "String");
            assert_eq!(gen_ref("(Base int ())"), "i32");
            assert_eq!(gen_ref("(Base int32 ())"), "i32");
        }

        #[test]
        fn base_type() {
            assert_eq!(gen_ref("(Base foo ())"), "foo");

            assert_eq!(gen_ref("(Base foo ((Base bar ())))"), "foo < bar >");
            assert_eq!(gen_ref("(Base option ((Base bar ())))"), "Option < bar >");
            assert_eq!(gen_ref("(Base list ((Base bar ())))"), "Vec < bar >");
            assert_eq!(gen_ref("(Base array ((Base bar ())))"), "Vec < bar >");
        }

        #[test]
        fn top_app_base_type() {
            let src = r#"(Top_app
 ((gid 167) (loc src/std_internal.ml:131:2)
  (members
   ((list
     ((a)
      (Top_app
       ((gid 50) (loc src/list0.ml:6:0)
        (members
         ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
       t ((Var (src/std_internal.ml:131:17 a)))))))))
 list
 ((Top_app
   ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
    (members
     ((t
       (()
        (Base foo ()
              ))))))
   t ())))"#;
            assert_eq!(gen_ref(src), "Vec < foo >");

            let src = r#"(Top_app
 ((gid 683) (loc src/lib/mina_base/transaction_status.ml:71:8)
  (members
   ((t
     (()
      (Top_app
       ((gid 167) (loc src/std_internal.ml:131:2)
        (members
         ((list
           ((a)
            (Top_app
             ((gid 50) (loc src/list0.ml:6:0)
              (members ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
             t ((Var (src/std_internal.ml:131:17 a)))))))))
       list
       ((Top_app
         ((gid 167) (loc src/std_internal.ml:131:2)
          (members
           ((list
             ((a)
              (Top_app
               ((gid 50) (loc src/list0.ml:6:0)
                (members
                 ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
               t ((Var (src/std_internal.ml:131:17 a)))))))))
         list
         ((Top_app
           ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
            (members
             ((t
               (()
                (Base foo ()
                 ))))))
           t ()))))))))))
 t ())"#;
            assert_eq!(gen_ref(src), "Vec < Vec < foo > >");
        }

        #[test]
        fn top_app() {
            // top_app without top-level name should be inlined
            assert_eq!(
                gen_ref(
                    r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#
                ),
                "String"
            );

            // top-level top_app should a type alias
            assert_eq!(
                gen_ref_top(
                    "top",
                    r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#
                ),
                "Top"
            );
        }
    }

    mod gen_type {
        use rust_format::{Formatter, RustFmt};

        use crate::{gen::GeneratorBuilder, shape::Expression, xref::XRef};

        fn gen_type(name: &str, expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding = [(name, expr.clone())];
            let xref = XRef::new(&binding).unwrap();
            let ts = GeneratorBuilder::default()
                .xref(&xref)
                .build()
                .unwrap()
                .generate_type(&expr);
            RustFmt::default().format_tokens(ts.into()).unwrap()
        }

        #[test]
        fn base() {
            let src = r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#;
            let rust = "pub type MyString = String;\n";
            assert_eq!(gen_type("MyString", src), rust);
        }

        #[test]
        fn record() {
            let src = r#"(Top_app
 ((gid 817) (loc src/lib/trust_system/record.ml:6:4)
  (members
   ((t
     (()
      (Record
       ((trust
         (Top_app
          ((gid 162) (loc src/std_internal.ml:116:2)
           (members
            ((float
              (()
               (Top_app
                ((gid 104) (loc src/float.ml:26:2)
                 (members ((t (() (Base float ()))))))
                t ()))))))
          float ()))
        (trust_last_updated
         (Top_app
          ((gid 104) (loc src/float.ml:26:2)
           (members ((t (() (Base float ()))))))
          t ())))))))))
 t ())"#;
            let rust = r#"pub struct MyRecord {
    pub trust: f32,
    pub trust_last_updated: f32,
}
"#;
            assert_eq!(gen_type("MyRecord", src), rust);
        }

        #[test]
        fn record_with_option() {
            let src = r#"(Top_app
 ((gid 817) (loc src/lib/trust_system/record.ml:6:4)
  (members
   ((t
     (()
      (Record
       ((trust
         (Top_app
          ((gid 162) (loc src/std_internal.ml:116:2)
           (members
            ((float
              (()
               (Top_app
                ((gid 104) (loc src/float.ml:26:2)
                 (members ((t (() (Base float ()))))))
                t ()))))))
          float ()))
        (trust_last_updated
         (Top_app
          ((gid 104) (loc src/float.ml:26:2)
           (members ((t (() (Base float ()))))))
          t ()))
        (banned_until_opt
         (Top_app
          ((gid 61) (loc src/option.ml:16:4)
           (members
            ((t
              ((a)
               (Top_app
                ((gid 60) (loc src/option.ml:4:0)
                 (members
                  ((t ((a) (Base option ((Var (src/option.ml:4:12 a)))))))))
                t ((Var (src/option.ml:16:23 a)))))))))
          t
          ((Top_app
            ((gid 104) (loc src/float.ml:26:2)
             (members ((t (() (Base float ()))))))
            t ())))))))))))
 t ())"#;
            let rust = r#"pub struct MyRecord {
    pub trust: f32,
    pub trust_last_updated: f32,
    pub banned_until_opt: Option<f32>,
}
"#;
            assert_eq!(gen_type("MyRecord", src), rust);
        }

        #[test]
        fn variant() {
            let src = r#"(Top_app
 ((gid 1052) (loc src/lib/vrf_evaluator/vrf_evaluator.ml:35:6)
  (members
   ((t
     (()
      (Variant
       ((At
         ((Top_app
           ((gid 539) (loc src/lib/mina_numbers/nat.ml:258:6)
            (members
             ((t
               (()
                (Top_app
                 ((gid 119) (loc src/int32.ml:6:6)
                  (members ((t (() (Base int32 ()))))))
                 t ()))))))
           t ())))
        (Completed ()))))))))
 t ())"#;
            let rust = r#"pub enum MyEnum {
    At(i32),
    Completed,
}
"#;
            assert_eq!(gen_type("MyEnum", src), rust);
        }

        #[test]
        fn tuple() {
            let src = r#"(Top_app
 ((gid 804) (loc src/lib/merkle_address/merkle_address.ml:48:6)
  (members
   ((t
     (()
      (Tuple
       ((Top_app
         ((gid 163) (loc src/std_internal.ml:119:2)
          (members
           ((int
             (()
              (Top_app
               ((gid 113) (loc src/int.ml:19:6)
                (members ((t (() (Base int ()))))))
               t ()))))))
         int ())
        (Top_app
         ((gid 170) (loc src/std_internal.ml:140:2)
          (members
           ((string
             (()
              (Top_app
               ((gid 83) (loc src/string.ml:44:6)
                (members ((t (() (Base string ()))))))
               t ()))))))
         string ()))))))))
 t ())"#;
            let rust = r#"pub type MyTuple = (i32, String);
"#;
            assert_eq!(gen_type("MyTuple", src), rust);
        }

        #[test]
        fn san_name() {
            let src = r#"(Top_app
 ((gid 804) (loc src/lib/merkle_address/merkle_address.ml:48:6)
  (members
   ((t
     (()
      (Tuple
       ((Top_app
         ((gid 163) (loc src/std_internal.ml:119:2)
          (members
           ((int
             (()
              (Top_app
               ((gid 113) (loc src/int.ml:19:6)
                (members ((t (() (Base int ()))))))
               t ()))))))
         int ())
        (Top_app
         ((gid 170) (loc src/std_internal.ml:140:2)
          (members
           ((string
             (()
              (Top_app
               ((gid 83) (loc src/string.ml:44:6)
                (members ((t (() (Base string ()))))))
               t ()))))))
         string ()))))))))
 t ())"#;
            let rust = r#"pub type MyTuple = (i32, String);
"#;
            assert_eq!(gen_type("My.tuple.t", src), rust);
        }
    }

    mod complex {
        use rust_format::{Formatter, RustFmt};

        use crate::{gen::GeneratorBuilder, shape::Expression, xref::XRef};

        fn gen_type(name: &str, types: &[(&str, &str)]) -> String {
            let bindings = types
                .iter()
                .map(|(n, e)| (n, e.parse::<Expression>().unwrap()))
                .collect::<Vec<_>>();
            let xref = XRef::new(&bindings).unwrap();
            let ts = GeneratorBuilder::default()
                .xref(&xref)
                // .generate_comments(true)
                // .git_prefix("https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/")
                .build()
                .unwrap()
                .generate(name)
                .unwrap();
            eprintln!("====\n{ts}\n====");
            let res = RustFmt::default().format_tokens(ts.into()).unwrap();
            eprintln!("====\n{res}\n====");
            res
        }

        #[test]
        fn collection() {
            let collection = r#"(Top_app
 ((gid 683) (loc src/lib/mina_base/transaction_status.ml:71:8)
  (members
   ((t
     (()
      (Top_app
       ((gid 167) (loc src/std_internal.ml:131:2)
        (members
         ((list
           ((a)
            (Top_app
             ((gid 50) (loc src/list0.ml:6:0)
              (members ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
             t ((Var (src/std_internal.ml:131:17 a)))))))))
       list
       ((Top_app
         ((gid 167) (loc src/std_internal.ml:131:2)
          (members
           ((list
             ((a)
              (Top_app
               ((gid 50) (loc src/list0.ml:6:0)
                (members
                 ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
               t ((Var (src/std_internal.ml:131:17 a)))))))))
         list
         ((Top_app
           ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
            (members
             ((t
               (()
                (Variant
                 ((Predicate ()) (Source_not_present ())
                  (Incorrect_nonce ()) (Invalid_fee_excess ()))))))))
           t ()))))))))))
 t ())"#;
            let item = r#"(Top_app
 ((gid 681) (loc src/lib/mina_base/transaction_status.ml:9:6)
  (members
   ((t
     (()
      (Variant
       ((Predicate ()) (Source_not_present ()) (Receiver_not_present ())
        (Invalid_fee_excess ()))))))))
 t ())"#;
            let rust = r#"pub type Collection = Vec<Vec<Item>>;
pub enum Item {
    Predicate,
    Source_not_present,
    Incorrect_nonce,
    Invalid_fee_excess,
}
"#;
            assert_eq!(
                gen_type("Collection", &[("Collection", collection), ("Item", item),],),
                rust
            );
        }

        #[test]
        fn inner_type() {
            let stack_versioned = r#"(Top_app
 ((gid 763) (loc src/lib/mina_base/pending_coinbase.ml:502:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 762) (loc src/lib/mina_base/pending_coinbase.ml:492:8)
        (members
         ((t
           ((data_stack state_stack)
            (Record
             ((data
               (Var
                (src/lib/mina_base/pending_coinbase.ml:493:19 data_stack)))
              (state
               (Var
                (src/lib/mina_base/pending_coinbase.ml:493:40 state_stack))))))))))
       t
       ((Top_app
         ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
          (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
         t ())
        (Top_app
         ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 752) (loc src/lib/mina_base/pending_coinbase.ml:236:8)
                (members
                 ((t
                   ((stack_hash)
                    (Record
                     ((init
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:236:38
                         stack_hash)))
                      (curr
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:236:58
                         stack_hash))))))))))
               t
               ((Top_app
                 ((gid 749) (loc src/lib/mina_base/pending_coinbase.ml:210:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ()))))))))
         t ()))))))))
 t ())"#;
            let state_stack = r#"(Top_app
 ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 752) (loc src/lib/mina_base/pending_coinbase.ml:236:8)
        (members
         ((t
           ((stack_hash)
            (Record
             ((init
               (Var
                (src/lib/mina_base/pending_coinbase.ml:236:38 stack_hash)))
              (curr
               (Var
                (src/lib/mina_base/pending_coinbase.ml:236:58 stack_hash))))))))))
       t
       ((Top_app
         ((gid 749) (loc src/lib/mina_base/pending_coinbase.ml:210:6)
          (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
         t ()))))))))
 t ())"#;
            let pending_coinbase_stack_state = r#"(Top_app
 ((gid 902) (loc src/lib/transaction_snark/transaction_snark.ml:92:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 901) (loc src/lib/transaction_snark/transaction_snark.ml:68:8)
        (members
         ((t
           ((pending_coinbase)
            (Record
             ((source
               (Var
                (src/lib/transaction_snark/transaction_snark.ml:69:21
                 pending_coinbase)))
              (target
               (Var
                (src/lib/transaction_snark/transaction_snark.ml:69:49
                 pending_coinbase))))))))))
       t
       ((Top_app
         ((gid 763) (loc src/lib/mina_base/pending_coinbase.ml:502:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 762) (loc src/lib/mina_base/pending_coinbase.ml:492:8)
                (members
                 ((t
                   ((data_stack state_stack)
                    (Record
                     ((data
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:19
                         data_stack)))
                      (state
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:40
                         state_stack))))))))))
               t
               ((Top_app
                 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ())
                (Top_app
                 ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
                  (members
                   ((t
                     (()
                      (Top_app
                       ((gid 752)
                        (loc src/lib/mina_base/pending_coinbase.ml:236:8)
                        (members
                         ((t
                           ((stack_hash)
                            (Record
                             ((init
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:38
                                 stack_hash)))
                              (curr
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:58
                                 stack_hash))))))))))
                       t
                       ((Top_app
                         ((gid 749)
                          (loc src/lib/mina_base/pending_coinbase.ml:210:6)
                          (members
                           ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                         t ()))))))))
                 t ()))))))))
         t ()))))))))
 t ())"#;
            let rust = r#"pub struct PendingCoinbaseStackState {
    pub source: StackVersioned,
    pub target: StackVersioned,
}
pub struct StackVersioned {
    pub data: kimchi_backend_bigint_32_V1,
    pub state: StateStack,
}
pub struct StateStack {
    pub init: kimchi_backend_bigint_32_V1,
    pub curr: kimchi_backend_bigint_32_V1,
}
"#;

            assert_eq!(
                gen_type(
                    "PendingCoinbaseStackState",
                    &[
                        ("PendingCoinbaseStackState", pending_coinbase_stack_state),
                        ("StackVersioned", stack_versioned),
                        ("StateStack", state_stack)
                    ],
                ),
                rust
            );
        }
        #[test]
        fn rec_app() {
            let src = r#"(Top_app
 ((gid 765) (loc src/lib/mina_base/pending_coinbase.ml:527:6)
  (members
   ((t
     (()
      (Top_app
       ((gid 598) (loc src/lib/sparse_ledger_lib/sparse_ledger.ml:38:6)
        (members
         ((t
           ((hash key account)
            (Record
             ((indexes
               (Top_app
                ((gid 167) (loc src/std_internal.ml:131:2)
                 (members
                  ((list
                    ((a)
                     (Top_app
                      ((gid 50) (loc src/list0.ml:6:0)
                       (members
                        ((t ((a) (Base list ((Var (src/list0.ml:6:12 a)))))))))
                      t ((Var (src/std_internal.ml:131:17 a)))))))))
                list
                ((Tuple
                  ((Var
                    (src/lib/sparse_ledger_lib/sparse_ledger.ml:39:21 key))
                   (Top_app
                    ((gid 163) (loc src/std_internal.ml:119:2)
                     (members
                      ((int
                        (()
                         (Top_app
                          ((gid 113) (loc src/int.ml:19:6)
                           (members ((t (() (Base int ()))))))
                          t ()))))))
                    int ()))))))
              (depth
               (Top_app
                ((gid 163) (loc src/std_internal.ml:119:2)
                 (members
                  ((int
                    (()
                     (Top_app
                      ((gid 113) (loc src/int.ml:19:6)
                       (members ((t (() (Base int ()))))))
                      t ()))))))
                int ()))
              (tree
               (Top_app
                ((gid 597)
                 (loc src/lib/sparse_ledger_lib/sparse_ledger.ml:9:6)
                 (members
                  ((t
                    ((hash account)
                     (Variant
                      ((Account
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:10:21
                           account))))
                       (Hash
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:11:18
                           hash))))
                       (Node
                        ((Var
                          (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:18
                           hash))
                         (Rec_app t
                          ((Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:27
                             hash))
                           (Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:34
                             account))))
                         (Rec_app t
                          ((Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:49
                             hash))
                           (Var
                            (src/lib/sparse_ledger_lib/sparse_ledger.ml:12:56
                             account)))))))))))))
                t
                ((Var
                  (src/lib/sparse_ledger_lib/sparse_ledger.ml:41:18 hash))
                 (Var
                  (src/lib/sparse_ledger_lib/sparse_ledger.ml:41:25 account))))))))))))
       t
       ((Top_app
         ((gid 764) (loc src/lib/mina_base/pending_coinbase.ml:515:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 756) (loc src/lib/mina_base/pending_coinbase.ml:356:6)
                (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
               t ()))))))
         t ())
        (Top_app
         ((gid 741) (loc src/lib/mina_base/pending_coinbase.ml:101:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 163) (loc src/std_internal.ml:119:2)
                (members
                 ((int
                   (()
                    (Top_app
                     ((gid 113) (loc src/int.ml:19:6)
                      (members ((t (() (Base int ()))))))
                     t ()))))))
               int ()))))))
         t ())
        (Top_app
         ((gid 763) (loc src/lib/mina_base/pending_coinbase.ml:502:6)
          (members
           ((t
             (()
              (Top_app
               ((gid 762) (loc src/lib/mina_base/pending_coinbase.ml:492:8)
                (members
                 ((t
                   ((data_stack state_stack)
                    (Record
                     ((data
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:19
                         data_stack)))
                      (state
                       (Var
                        (src/lib/mina_base/pending_coinbase.ml:493:40
                         state_stack))))))))))
               t
               ((Top_app
                 ((gid 744) (loc src/lib/mina_base/pending_coinbase.ml:150:6)
                  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                 t ())
                (Top_app
                 ((gid 753) (loc src/lib/mina_base/pending_coinbase.ml:245:6)
                  (members
                   ((t
                     (()
                      (Top_app
                       ((gid 752)
                        (loc src/lib/mina_base/pending_coinbase.ml:236:8)
                        (members
                         ((t
                           ((stack_hash)
                            (Record
                             ((init
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:38
                                 stack_hash)))
                              (curr
                               (Var
                                (src/lib/mina_base/pending_coinbase.ml:236:58
                                 stack_hash))))))))))
                       t
                       ((Top_app
                         ((gid 749)
                          (loc src/lib/mina_base/pending_coinbase.ml:210:6)
                          (members
                           ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
                         t ()))))))))
                 t ()))))))))
         t ()))))))))
 t ())"#;
            let rust = r#"pub struct MyType {
    pub indexes: Vec<(i32, i32)>,
    pub depth: i32,
    pub tree: MyTypeFieldtree,
}
pub enum MyTypeFieldtree {
    Account(MyTypeArg0),
    Hash(kimchi_backend_bigint_32_V1),
    Node(
        kimchi_backend_bigint_32_V1,
        MyTypeFieldtree,
        MyTypeFieldtree,
    ),
}
pub struct MyTypeArg0 {
    pub data: kimchi_backend_bigint_32_V1,
    pub state: MyTypeArg0Arg0,
}
pub struct MyTypeArg0Arg0 {
    pub init: kimchi_backend_bigint_32_V1,
    pub curr: kimchi_backend_bigint_32_V1,
}
"#;
            assert_eq!(gen_type("MyType", &[("MyType", src)]), rust);
        }
    }

    #[test]
    fn test() {
        use proc_macro2::TokenStream;
        use quote::quote;
        use rust_format::{Formatter, RustFmt};
        let err =
            syn::Error::new(proc_macro2::Span::call_site(), "error, error").to_compile_error();

        let ts = quote!(type Foo = Vec<#err>;);
        let res = RustFmt::default().format_tokens(ts.into()).unwrap();

        println!("{res}");
    }
}
