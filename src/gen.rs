use std::collections::HashMap;

use derive_builder::Builder;
use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use serde::{Deserialize, Serialize};
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

macro_rules! some_or_gen_error {
    ($expr:expr, $fmt:literal $(, $($arg:tt)*)?) => {
        match $expr {
            Some(v) => v,
            None => return gen_error!($fmt, $( $($arg)*)?),
        }
    };
    ($expr:expr, $err:expr) => {
        match $expr {
            Some(v) => v,
            None => return $err.into(),
        }
    };
}

macro_rules! ok_or_gen_error {
    ($expr:expr) => {
        match $expr {
            Ok(v) => v,
            Err(e) => return e.into(),
        }
    };
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
    #[error("No name for group {0}")]
    UnknownGroupName(&'a Gid),
    #[error("Unresolved type variable {0}")]
    UnresolvedTypeVar(&'a str),
    #[error("Unresolved recursive type reference {0}")]
    UnresolvedRecType(&'a str),
    #[error("Assertion failed: {0}")]
    Assert(String),
}

impl<'a> From<Error<'a>> for TokenStream {
    fn from(source: Error<'a>) -> Self {
        gen_error!("{source}")
    }
}

#[derive(Serialize, Deserialize, Builder)]
pub struct Config {
    /// Generate comments.
    #[builder(default)]
    generate_comments: bool,

    /// Add blank line markers between types.
    #[builder(default)]
    blank_lines: bool,

    /// Git repository prefix
    #[builder(setter(into, strip_option), default)]
    git_prefix: Option<String>,

    /// Wrap internal types into specific generic
    wrap_internal_types: bool,

    /// Rust file preamble.
    #[builder(default)]
    #[serde(with = "token_stream")]
    preamble: TokenStream,

    /// Type preamble, like attributes.
    #[builder(default)]
    #[serde(with = "token_stream")]
    type_preamble: TokenStream,

    /// Base types mapping.
    #[builder(default = "base_types()")]
    base_types: HashMap<String, BaseTypeMapping>,
}

mod token_stream {
    use proc_macro2::TokenStream;
    use serde::{de::Visitor, Deserializer, Serializer};

    pub fn serialize<S>(ts: &TokenStream, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&ts.to_string())
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<TokenStream, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = TokenStream;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Rust token stream")
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                v.parse().map_err(|e| E::custom(format!("lexer error {e}")))
            }
        }

        deserializer.deserialize_str(V)
    }
}

/// Status of a type generationl.
enum TypeStatus {
    /// Type is referenced using this name and its generation is pending.
    Pending(String),
    /// Type is already generated with the specified name.
    Generated(String),
}

impl TypeStatus {
    fn type_name(&self) -> &str {
        match self {
            TypeStatus::Pending(name) | TypeStatus::Generated(name) => name.as_str(),
        }
    }
}

pub struct Generator<'a> {
    /// Type expression name/id information.
    xref: &'a XRef<'a>,

    /// Generator configuration.
    config: Config,

    /// Group to type name mapping.
    name_mapping: HashMap<&'a Gid, TypeStatus>,

    /// Artifical names already in use.
    used_names: HashMap<String, u8>,

    /// Additional types referenced by main ones.
    aux_types: TokenStream,

    /// Type variables substitution.
    venv: Venv<'a>,
    /// Types substitution (for recursive types).
    tenv: Tenv<'a>,
}

pub type Result<'a, T = ()> = std::result::Result<T, Error<'a>>;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BaseTypeArgs {
    None,
    Single,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BaseTypeMapping {
    #[serde(with = "token_stream")]
    pub rust_id: TokenStream,
    pub args_num: BaseTypeArgs,
}

impl<'a> Generator<'a> {
    pub fn new(xref: &'a XRef<'a>, config: Config) -> Self {
        Self {
            xref,
            config,
            name_mapping: HashMap::new(),
            used_names: HashMap::new(),
            aux_types: TokenStream::new(),
            venv: HashMap::new(),
            tenv: HashMap::new(),
        }
    }

    pub fn generate_types<T, I>(&mut self, types: I) -> TokenStream
    where
        T: 'a + AsRef<str>,
        I: IntoIterator<Item = T>,
    {
        let mut ts = types
            .into_iter()
            .fold(self.config.preamble.clone(), |mut ts, name| {
                ts.extend(self.generate_for_name(name.as_ref()));
                if self.config.blank_lines {
                    ts.extend(quote!(_blank_!();));
                }
                ts
            });
        ts.extend(std::mem::take(&mut self.aux_types));
        ts
    }

    pub fn generate(&mut self, name: &str) -> TokenStream {
        let mut ts = self.config.preamble.clone();

        self.generate_for_name(name).to_tokens(&mut ts);
        std::mem::take(&mut self.aux_types).to_tokens(&mut ts);
        ts
    }

    fn generate_for_name(&mut self, name: &str) -> TokenStream {
        const EMPTY: &[Vid] = &[];
        let ts = self.xref.expr_for_name(name).map_or_else(
            || Error::TypeNotFound(name.to_string()).into(),
            |expr| self.generate_type(None, expr, EMPTY),
        );
        //println!("{name} ==> {ts}");
        ts
    }

    fn add_aux_type(&mut self, ts: TokenStream) {
        if self.config.blank_lines {
            self.aux_types.extend(quote!(_blank_!();));
        }
        //println!("==> {ts}");
        self.aux_types.extend(ts);
    }

    fn generate_type(
        &mut self,
        type_name: Option<&str>,
        expr: &'a Expression,
        params: &[Vid],
    ) -> TokenStream {
        match expr {
            Expression::Annotate(_, _) => todo!(),
            Expression::Base(uuid, args) => self.generate_base_type(type_name, uuid, args, params),
            Expression::Record(exprs) => self.generate_record(type_name, exprs, params),
            Expression::Variant(alts) => self.generate_variant(type_name, alts, params),
            Expression::Tuple(exprs) => self.generate_tuple(type_name, exprs, params),
            Expression::Poly_variant((loc, constrs)) => {
                self.generate_poly_variant(type_name, loc, constrs, params)
            }
            Expression::Var((loc, vid)) => self.generate_var(type_name, loc, vid),
            Expression::Rec_app(tid, args) => self.generate_rec_app(type_name, tid, args, params),
            Expression::Top_app(group, tid, args) => {
                self.generate_top_app(type_name, group, tid, args)
            }
        }
    }

    fn params(&self, params: &[Vid]) -> Option<TokenStream> {
        if params.is_empty() {
            return None;
        }
        let params = params
            .iter()
            .map(|vid| format_ident!("{}", self.sanitize_name(vid)));
        Some(quote! {
            < #(#params),* >
        })
    }

    fn generate_base_type(
        &mut self,
        type_name: Option<&str>,
        uuid: &str,
        args: &'a [Expression],
        params: &[Vid],
    ) -> TokenStream {
        let type_name =
            some_or_gen_error!(type_name, Error::Assert(format!("No name for base type")));
        let preamble = self.config.type_preamble.clone();
        let args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| self.type_reference(Some(&format!("{type_name}Arg{i}")), arg))
            .collect::<Vec<_>>();
        let base = self.base_type_mapping(uuid, &args);
        let name = format_ident!("{type_name}");
        let params = self.params(params);
        quote! {
            #preamble
            pub struct #name #params (pub #base);
        }
    }

    fn generate_record(
        &mut self,
        type_name: Option<&str>,
        fields: &'a [(String, Expression)],
        params: &[Vid],
    ) -> TokenStream {
        let type_name =
            some_or_gen_error!(type_name, Error::Assert(format!("No name for record type")));
        let name = format_ident!("{type_name}");
        let preamble = self.config.type_preamble.clone();
        let phantom_fields = self.get_unused_params(fields.iter().map(|(_, expr)| expr), params);
        let phantom_fields = phantom_fields
            .iter()
            .enumerate()
            .map(|(i, vid)| self.generate_phantom_field(i, vid))
            .collect::<Vec<_>>();
        let params = self.params(params);
        let fields = fields
            .iter()
            .map(|(field, expr)| self.generate_field(type_name, field, expr, true))
            .chain(phantom_fields);
        quote! {
            #preamble
            pub struct #name #params {
                #(#fields,)*
            }
        }
    }

    fn get_unused_params<I: Clone + IntoIterator<Item = &'a Expression>>(
        &self,
        exprs: I,
        params: &'a [Vid],
    ) -> Vec<&'a Vid> {
        params
            .iter()
            .filter(|vid| !self.is_used(vid, exprs.clone()))
            .collect()
    }

    fn is_used<I: IntoIterator<Item = &'a Expression>>(&self, vid: &'a Vid, exprs: I) -> bool {
        exprs.into_iter().any(|expr| self.is_used_in(vid, expr))
    }

    fn is_used_in(&self, vid: &'a Vid, expr: &Expression) -> bool {
        match expr {
            Expression::Annotate(_, expr) => self.is_used_in(vid, expr.as_ref()),
            Expression::Base(_, exprs) => self.is_used(vid, exprs.iter()),
            Expression::Record(fields) => self.is_used(vid, fields.iter().map(|(_, expr)| expr)),
            Expression::Variant(alts) => {
                self.is_used(vid, alts.iter().flat_map(|(_, expr)| expr.iter()))
            }
            Expression::Tuple(exprs) => self.is_used(vid, exprs.iter()),
            Expression::Poly_variant(_) => false,
            Expression::Var((_, v)) => vid == v,
            Expression::Rec_app(_, _) => false,
            Expression::Top_app(_, _, args) => self.is_used(vid, args.iter()),
        }
    }

    fn generate_field(
        &mut self,
        type_name: &str,
        field: &str,
        expr: &'a Expression,
        make_public: bool,
    ) -> TokenStream {
        let field_name = format_ident!("{field}");
        let field_type = self.type_reference(
            Some(&format!(
                "{type_name}{field}",
                field = self.sanitize_name(field)
            )),
            expr,
        );
        let p = if make_public { quote!(pub) } else { quote!() };
        quote! {
            #p #field_name: #field_type
        }
    }

    fn generate_phantom_field(&self, i: usize, vid: &Vid) -> TokenStream {
        let field_name = format_ident!("_phantom_data_{}", i.to_string());
        let type_name = format_ident!("{}", self.sanitize_name(vid));
        quote! {
            #field_name: PhantomData< #type_name >
        }
    }

    fn generate_variant(
        &mut self,
        type_name: Option<&str>,
        alts: &'a [(String, Vec<Expression>)],
        params: &[Vid],
    ) -> TokenStream {
        let type_name = some_or_gen_error!(
            type_name,
            Error::Assert(format!("No name for variant type"))
        );
        let name = format_ident!("{type_name}");
        let preamble = self.config.type_preamble.clone();
        let params = self.params(params);
        let alts = alts
            .iter()
            .map(|(alt, exprs)| self.generate_alternative(type_name, alt, exprs));
        quote! {
            #preamble
            pub enum #name #params {
                #(
                    #alts,
                )*
            }
        }
    }

    fn generate_alternative(
        &mut self,
        type_name: &str,
        alt: &str,
        exprs: &'a [Expression],
    ) -> TokenStream {
        let alt = self.sanitize_name(alt);
        let alt_name = format_ident!("{alt}");
        if exprs.is_empty() {
            quote!(#alt_name)
        } else if let Some((Expression::Record(fields), [])) = exprs.split_first() {
            let fields = fields
                .iter()
                .map(|(name, expr)| self.generate_field(&alt, name, expr, false));
            quote! {
                #alt_name {
                    #(#fields,)*
                }
            }
        } else {
            let exprs = exprs
                .iter()
                .enumerate()
                .map(|(i, expr)| self.type_reference(Some(&format!("{type_name}{alt}{i}")), expr));
            quote!(#alt_name(#(#exprs,)*))
        }
    }

    fn generate_tuple(
        &mut self,
        type_name: Option<&str>,
        exprs: &'a [Expression],
        params: &[Vid],
    ) -> TokenStream {
        let type_name =
            some_or_gen_error!(type_name, Error::Assert(format!("No name for tuple type")));
        let name = format_ident!("{type_name}");
        let preamble = self.config.type_preamble.clone();
        let params = self.params(params);
        let exprs = exprs
            .iter()
            .enumerate()
            .map(|(i, expr)| self.type_reference(Some(&format!("{type_name}{i}")), expr));
        quote! {
            #preamble
            pub struct #name #params (#(pub #exprs,)*);
        }
    }

    fn generate_poly_variant(
        &mut self,
        type_name: Option<&str>,
        _loc: &Location,
        constrs: &'a [PolyConstr],
        params: &[Vid],
    ) -> TokenStream {
        let type_name =
            some_or_gen_error!(type_name, Error::Assert(format!("No name for tuple type")));
        let name = format_ident!("{type_name}");
        let preamble = self.config.type_preamble.clone();
        let params = self.params(params);
        let constrs = constrs
            .iter()
            .map(|constr| self.generate_poly_constr(type_name, constr));
        quote! {
            #preamble
            pub enum #name #params {
                #(#constrs,)*
            }
        }
    }

    fn generate_poly_constr(&mut self, type_name: &str, constr: &'a PolyConstr) -> TokenStream {
        match constr {
            PolyConstr::Constr((name, opt_expr)) => {
                let constr_name = format_ident!("{name}");
                if let Some(expr) = opt_expr {
                    let expr = self.type_reference(Some(&format!("{type_name}{name}")), expr);
                    quote!(#constr_name(#expr))
                } else {
                    quote!(#constr_name)
                }
            }
            PolyConstr::Inherit(_) => {
                Error::Assert(format!("poly constr inherit is not implemented")).into()
            }
        }
    }

    fn generate_var(&mut self, _type_name: Option<&str>, loc: &str, vid: &str) -> TokenStream {
        gen_error!("Unexpanded type variable {vid} at {loc}")
    }

    fn generate_rec_app(
        &mut self,
        _type_name: Option<&str>,
        tid: &str,
        _args: &[Expression],
        _params: &[Vid],
    ) -> TokenStream {
        gen_error!("Unexpected recursive application of type {tid}")
    }

    fn generate_top_app(
        &mut self,
        type_name: Option<&str>,
        group: &'a Group,
        _tid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        let Group { gid, loc: _, members } = group;
        let named = !self.xref.is_anonymous(*gid);
        if named {
            if let Some(TypeStatus::Generated(_)) = self.name_mapping.get(gid) {
                return quote!();
            }
        }

        let type_name = if named {
            self.sanitize_name(some_or_gen_error!(
                self.group_name(gid).or(type_name),
                Error::UnknownGroupName(gid)
            ))
        } else {
            some_or_gen_error!(type_name, Error::UnknownGroupName(gid)).to_string()
        };

        self.name_mapping
            .insert(gid, TypeStatus::Generated(type_name.clone()));

        let (tid, (_vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        if let Some(ver_expr) = self.versioned_type(expr) {
            self.generate_versioned_top_app(&type_name, group, tid, args, ver_expr)
        } else {
            self.generate_plain_top_app(&type_name, group, tid, args)
        }
    }

    fn generate_versioned_top_app(
        &mut self,
        type_name: &str,
        group: &'a Group,
        _tid: &str,
        _args: &'a [Expression],
        ver_expr: &'a Expression,
    ) -> TokenStream {
        let Group { gid, loc, members } = group;
        let (_tid, (vids, _expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        let comment = self.generate_doc_comment(gid, loc);
        let type_ref = self.type_reference(Some(&format!("{type_name}Ver")), ver_expr);
        let type_name = format_ident!("{type_name}");
        let params = self.params(vids);
        quote! {
            #comment
            pub type #type_name #params = Versioned<#type_ref, 1>;
        }
    }

    fn generate_plain_top_app(
        &mut self,
        type_name: &str,
        group: &'a Group,
        _tid: &str,
        _args: &'a [Expression],
    ) -> TokenStream {
        let Group { gid, loc, members } = group;
        let (tid, (vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        // let venv = ok_or_gen_error!(self.new_venv(&group.gid, vids, args, Some(&type_name)));
        let tenv = self.new_tenv(gid, tid, Some(&type_name));

        let expr = if matches!(expr, Expression::Top_app(..)) {
            let type_ref = self.type_reference(Some(&format!("{type_name}Poly")), expr);
            let type_name = format_ident!("{type_name}");
            let comment = self.generate_doc_comment(gid, loc);
            let preamble = self.config.type_preamble.clone();
            let params = self.params(vids);
            quote! {
                #comment
                #preamble
                pub struct #type_name #params (pub #type_ref);
            }
        } else {
            let expr = self.generate_type(Some(&type_name), expr, vids);
            let comment = self.generate_doc_comment(gid, loc);
            quote! {
                #comment
                #expr
            }
        };

        self.tenv = tenv;

        expr
    }

    fn versioned_type(&self, expr: &'a Expression) -> Option<&'a Expression> {
        if let Expression::Record(fields) = expr {
            if fields.len() == 2 && &fields[0].0 == "version" && &fields[1].0 == "t" {
                let expr = &fields[1].1;
                if let Expression::Top_app(group, _, _) = expr {
                    if let Some((_, (_, inner_expr))) = group.members.first() {
                        if matches!(inner_expr, Expression::Top_app(inner_group, _, _) if &group.loc == &inner_group.loc)
                        {
                            return Some(inner_expr);
                        }
                    }
                }
                return Some(expr);
            }
        }
        None
    }

    fn git_loc(&self, loc: &str) -> Option<String> {
        let prefix = self.config.git_prefix.as_ref()?;
        let mut it = loc.split(':');
        let file = it.next()?;
        let line = it.next()?;
        Some(format!("[{loc}]({prefix}{file}#L{line})",))
    }

    fn generate_doc_comment(&self, gid: &Gid, loc: &str) -> TokenStream {
        if !self.config.generate_comments {
            return quote!();
        }
        let git_loc = self.git_loc(loc);
        let loc = git_loc.as_ref().map(String::as_str).unwrap_or(loc);
        let doc = if let Some(name) = self.xref.for_gid(*gid).and_then(|(_, name)| name) {
            format!(" **Origin**: `{name}`\n\n **Location**: {loc}")
        } else {
            format!(" Location: {loc}")
        };
        quote! {
            #[doc = #doc]
        }
    }

    //              type reference

    fn type_reference(&mut self, name_hint: Option<&str>, expr: &'a Expression) -> TokenStream {
        match expr {
            Expression::Annotate(uuid, expr) => {
                self.type_reference_annotation(name_hint, uuid, expr)
            }
            Expression::Base(uuid, args) => self.type_reference_base(name_hint, uuid, args),
            Expression::Record(fields) => self.type_reference_record(name_hint, fields),
            Expression::Variant(alts) => self.type_reference_variant(name_hint, alts),
            Expression::Tuple(exprs) => self.type_reference_tuple(name_hint, exprs),
            Expression::Poly_variant((loc, consts)) => {
                self.type_reference_poly_variant(name_hint, loc, consts)
            }
            Expression::Var((loc, vid)) => self.type_reference_var(name_hint, loc, vid),
            Expression::Rec_app(tid, args) => self.type_reference_rec_app(name_hint, tid, args),
            Expression::Top_app(group, tid, args) => {
                self.type_reference_top_app(name_hint, group, tid, args)
            }
        }
    }

    fn type_reference_annotation(
        &self,
        _name_hint: Option<&str>,
        _uuid: &str,
        _expr: &Expression,
    ) -> TokenStream {
        todo!()
    }

    fn type_reference_base(
        &mut self,
        name_hint: Option<&str>,
        uuid: &'a str,
        args: &'a [Expression],
    ) -> TokenStream {
        let type_name = name_hint.unwrap_or("UnknownBaseType");
        let args = args
            .iter()
            .enumerate()
            .map(|(i, arg)| self.type_reference(Some(&format!("{type_name}Arg{i}")), arg))
            .collect::<Vec<_>>();
        self.base_type_mapping(uuid, &args)
    }

    fn type_reference_record(
        &self,
        _name_hint: Option<&str>,
        _fields: &[(String, Expression)],
    ) -> TokenStream {
        gen_error!("Cannot reference record")
    }

    fn type_reference_variant(
        &self,
        _name_hint: Option<&str>,
        _alts: &[(String, Vec<Expression>)],
    ) -> TokenStream {
        gen_error!("Cannot reference variant")
    }

    fn type_reference_tuple(
        &mut self,
        name_hint: Option<&str>,
        exprs: &'a [Expression],
    ) -> TokenStream {
        let exprs = exprs
            .iter()
            .map(|expr| self.type_reference(name_hint, expr));
        quote!((#(#exprs),*))
    }

    fn type_reference_poly_variant(
        &mut self,
        name_hint: Option<&str>,
        _loc: &str,
        _constrs: &[PolyConstr],
    ) -> TokenStream {
        let name = some_or_gen_error!(
            name_hint,
            Error::Assert("issue with poly_variant".to_string())
        );
        format_ident!("{name}").to_token_stream()
    }

    fn type_reference_var(&self, _name_hint: Option<&str>, _loc: &str, vid: &str) -> TokenStream {
        self.venv
            .get(vid)
            .cloned()
            .unwrap_or_else(|| format_ident!("{}", self.sanitize_name(vid)).to_token_stream())
        //some_or_gen_error!(self.venv.get(vid).cloned(), Error::UnresolvedTypeVar(vid))
        //format_ident!("{}", self.sanitize_name(vid)).to_token_stream()
    }

    fn type_reference_rec_app(
        &mut self,
        _name_hint: Option<&str>,
        tid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        let type_name =
            some_or_gen_error!(self.tenv.get(tid).cloned(), Error::UnresolvedRecType(tid));
        let args = args.iter().map(|expr| self.type_reference(None, expr));
        quote! {
            #type_name < #( #args ),* >
        }
    }

    fn is_external_type(&self, loc: &Location) -> bool {
        const PREFIXES: &[&str] = &["src/lib/", "src/app"];
        PREFIXES.iter().all(|p| !loc.starts_with(p))
    }

    fn type_reference_top_app(
        &mut self,
        name_hint: Option<&str>,
        group: &'a Group,
        _tid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        let Group { gid, loc, members } = group;
        let (_tid, (vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(gid));

        if self.is_external_type(loc) {
            let venv = ok_or_gen_error!(self.new_venv(gid, vids, args, name_hint));
            let res = self.type_reference(name_hint, expr);
            self.venv = venv;
            return res;
        }

        let type_name = match self.name_mapping.get(gid) {
            Some(TypeStatus::Generated(name)) | Some(TypeStatus::Pending(name)) => {
                //println!("{gid} => {name}");
                name.to_string()
            }
            None => {
                let mut type_name = self.sanitize_name(some_or_gen_error!(
                    self.group_name(gid).or(name_hint),
                    Error::UnknownGroupName(gid)
                ));
                if let Some(existing) = self.used_names.get_mut(&type_name) {
                    type_name = format!("{type_name}Dup{existing}");
                    *existing += 1;
                } else {
                    self.used_names.insert(type_name.clone(), 0);
                }
                self.name_mapping
                    .insert(gid, TypeStatus::Pending(type_name.clone()));
                let ts = self.generate_top_app(Some(&type_name), group, loc, args);
                self.add_aux_type(ts);
                type_name
            }
        };
        let name = format_ident!("{type_name}");

        let args = if args.is_empty() {
            None
        } else {
            let args = args.iter().enumerate().map(|(i, arg)| {
                let type_name = format!("{name}Arg{i}");
                self.type_reference(Some(&type_name), arg)
            });
            Some(quote!(< #(#args),*>))
        };

        quote! {
            #name #args
        }
    }

    fn new_venv(
        &mut self,
        gid: &'a i32,
        vids: &'a [String],
        args: &'a [Expression],
        type_name: Option<&str>,
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
            .enumerate()
            .map(|(i, arg)| {
                if let Some(name) = type_name {
                    let type_name = format!("{name}Arg{i}");
                    self.type_reference(Some(&type_name), arg)
                } else {
                    self.type_reference(None, arg)
                }
            })
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

    fn new_tenv(
        &mut self,
        _gid: &'a i32,
        tid: &'a str,
        type_name: Option<&str>,
    ) -> HashMap<&'a str, TokenStream> {
        let mut tenv = self.tenv.clone();
        if let Some(name) = type_name {
            tenv.insert(tid, format_ident!("{name}").to_token_stream());
        }
        std::mem::replace(&mut self.tenv, tenv)
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
        if let Some(mapping) = self.config.base_types.get(uuid) {
            let name = mapping.rust_id.clone();
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
            .or_else(|| self.name_mapping.get(gid).map(TypeStatus::type_name))
    }
}

macro_rules! t {
    ($name:ident) => {
        (
            String::from(stringify!($name)),
            {
                let ident = format_ident!("{}", stringify!($name));
                BaseTypeMapping {
                    rust_id: ident.to_token_stream(),
                    args_num: BaseTypeArgs::None,
                }
            },
        )
    };
    ($name:ident => $($rust_toks:tt)*) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping {
                rust_id: stringify!($($rust_toks)*).parse().unwrap(),
                args_num: BaseTypeArgs::None,
            },
        )
    };
    ($name:ident < _ > => $($rust_toks:tt)*) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping {
                rust_id: stringify!($($rust_toks)*).parse().unwrap(),
                args_num: BaseTypeArgs::Single,
            },
        )
    };
}

fn base_types() -> HashMap<String, BaseTypeMapping> {
    HashMap::from([
        t!(bool),
        t!(unit => ()),
        t!(int => i32),
        t!(int32 => i32),
        t!(int64 => i64),
        t!(float => f32),
        t!(string => String),
        t!(option<_> => Option),
        t!(array<_> => Vec),
        t!(list<_> => Vec),
        t!(kimchi_backend_bigint_32_V1 => BigInt),
    ])
}

#[cfg(test)]
mod tests {

    mod type_ref {
        use crate::{
            gen::{ConfigBuilder, Generator},
            shape::Expression,
            xref::XRef,
        };

        fn gen_ref(expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding: [(String, Expression); 0] = [];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
                .type_reference(None, &expr);
            ts.to_string()
        }

        fn gen_ref_top(name: &str, expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding = [(name, expr.clone())];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
                .type_reference(None, &expr);
            ts.to_string()
        }

        #[test]
        fn base_type_builtins() {
            assert_eq!(gen_ref("(Base bool ())"), "bool");
            assert_eq!(gen_ref("(Base string ())"), "String");
            assert_eq!(gen_ref("(Base int ())"), "i32");
            assert_eq!(gen_ref("(Base int32 ())"), "i32");
            assert_eq!(gen_ref("(Base unit ())"), "()");
            assert_eq!(gen_ref("(Base kimchi_backend_bigint_32_V1 ())"), "BigInt");
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
   ((gid 681) (loc src/lib1/mina_base/transaction_status.ml:9:6)
    (members
     ((t
       (()
        (Base foo ()))))))
   t ())))"#;
            assert_eq!(gen_ref(src), "Vec < foo >");

            let src = r#"(Top_app
 ((gid 683) (loc src/lib1/mina_base/transaction_status.ml:71:8)
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
           ((gid 681) (loc src/lib1/mina_base/transaction_status.ml:9:6)
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

    mod others {
        use rust_format::{Formatter, RustFmt};

        use crate::{
            gen::{ConfigBuilder, Generator},
            shape::Expression,
            xref::XRef,
        };

        #[test]
        fn preamble() {
            let preamble = "pub type BigInt = [u8; 32];";
            let expr = r#"(Top_app
 ((gid 586) (loc src/lib/data_hash_lib/state_hash.ml:42:4)
  (members ((t (() (Base kimchi_backend_bigint_32_V1 ()))))))
 t ())"#;
            let rust = r#"pub type BigInt = [u8; 32];
pub struct MyType(pub BigInt);
"#;
            let expr: Expression = expr.parse().unwrap();
            let binding = [("MyType", expr.clone())];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(
                &xref,
                ConfigBuilder::default()
                    .preamble(preamble.parse().unwrap())
                    .build()
                    .unwrap(),
            )
            .generate("MyType");
            eprintln!("{ts}");
            let rust_act = RustFmt::default().format_tokens(ts.into()).unwrap();
            assert_eq!(rust, rust_act);
        }
    }

    mod gen_type {
        use rust_format::{Formatter, RustFmt};

        use crate::{
            gen::{ConfigBuilder, Generator},
            shape::Expression,
            xref::XRef,
        };

        fn gen_type(name: &str, expr: &str) -> String {
            let expr: Expression = expr.parse().unwrap();
            let binding = [(name, expr.clone())];
            let xref = XRef::new(&binding).unwrap();
            let ts = Generator::new(&xref, ConfigBuilder::default().build().unwrap())
                .generate_type(None, &expr, &[]);
            eprintln!("{ts}");
            let res = RustFmt::default().format_tokens(ts.into()).unwrap();
            eprintln!("===\n{res}===");
            res
        }

        #[test]
        fn base() {
            let src = r#"(Top_app
             ((gid 83) (loc src/string.ml:44:6)
              (members ((t (() (Base string ()))))))
             t ())"#;
            let rust = "pub struct MyString(pub String);\n";
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
    pub trust: MyRecordTrust,
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
    pub trust: MyRecordTrust,
    pub trust_last_updated: f32,
    pub banned_until_opt: MyRecordBannedUntilOpt<f32>,
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
    At(MyEnumAt0),
    Completed,
}
"#;
            assert_eq!(gen_type("MyEnum", src), rust);
        }

        #[test]
        fn variant_with_fields() {
            let src = r#"(Top_app
 ((gid 630) (loc src/lib/mina_base/stake_delegation.ml:9:4)
  (members
   ((t
     (()
      (Variant
       ((Set_delegate
         ((Record
           ((delegator
             (Base int ()))
            (new_delegate
             (Base int ())))))))))))))
 t ())"#;
            let rust = r#"pub enum MyEnum {
    SetDelegate { delegator: i32, new_delegate: i32 },
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
            let rust = r#"pub struct MyTuple(pub MyTuple0, pub MyTuple1);
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
            let rust = r#"pub struct MyTuple(pub MyTuple0, pub MyTuple1);
"#;
            assert_eq!(gen_type("My.tuple.t", src), rust);
        }
    }

    mod complex {
        use rust_format::{Formatter, RustFmt};

        use crate::{
            gen::{ConfigBuilder, Generator},
            shape::Expression,
            xref::XRef,
        };

        fn gen_type(name: &str, types: &[(&str, &str)]) -> String {
            let bindings = types
                .iter()
                .map(|(n, e)| (n, e.parse::<Expression>().unwrap()))
                .collect::<Vec<_>>();
            let xref = XRef::new(&bindings).unwrap();
            let ts = Generator::new(
                &xref,
                ConfigBuilder::default()
                    // .generate_comments(true)
                    // .git_prefix("https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/")
                    .build()
                    .unwrap(),
            )
            .generate(name);
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
                 ((Predicate ()) (Source_not_present ()) (Receiver_not_present ())
                  (Invalid_fee_excess ()))))))))
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
            let rust = r#"pub struct Collection(pub CollectionPoly<CollectionPoly<Item>>);
pub struct CollectionPoly<A>(pub Vec<A>);
pub enum Item {
    Predicate,
    SourceNotPresent,
    ReceiverNotPresent,
    InvalidFeeExcess,
}
"#;
            assert_eq!(
                gen_type("Collection", &[("Collection", collection), ("Item", item),],),
                rust
            );
        }

        #[test]
        fn poly_type() {
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
            let rust = r#"pub struct StateStack(pub StateStackPoly<StateStackPolyArg0>);
pub struct StateStackPoly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct StateStackPolyArg0(pub BigInt);
"#;

            assert_eq!(
                gen_type("StateStack", &[("StateStack", state_stack)],),
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
            let rust = r#"pub struct PendingCoinbaseStackState(pub PendingCoinbaseStackStatePoly<StackVersioned>);
pub struct PendingCoinbaseStackStatePoly<PendingCoinbase> {
    pub source: PendingCoinbase,
    pub target: PendingCoinbase,
}
pub struct StackVersionedPoly<DataStack, StateStack> {
    pub data: DataStack,
    pub state: StateStack,
}
pub struct StackVersionedPolyArg0(pub BigInt);
pub struct StateStackPoly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct StateStackPolyArg0(pub BigInt);
pub struct StateStack(pub StateStackPoly<StateStackPolyArg0>);
pub struct StackVersioned(pub StackVersionedPoly<StackVersionedPolyArg0, StateStack>);
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
            let rust = r#"pub struct MyType(pub MyTypePoly<MyTypePolyArg0, MyTypePolyArg1, MyTypePolyArg2>);
pub struct MyTypePolyIndexes<A>(pub Vec<A>);
pub struct MyTypePolyIndexesArg0(pub i32);
pub enum MyTypePolyTree<Hash, Account> {
    Account(Account),
    Hash(Hash),
    Node(
        Hash,
        MyTypePolyTree<Hash, Account>,
        MyTypePolyTree<Hash, Account>,
    ),
}
pub struct MyTypePoly<Hash, Key, Account> {
    pub indexes: MyTypePolyIndexes<(Key, MyTypePolyIndexesArg0)>,
    pub depth: MyTypePolyIndexesArg0,
    pub tree: MyTypePolyTree<Hash, Account>,
}
pub struct MyTypePolyArg0(pub BigInt);
pub struct MyTypePolyArg1(pub MyTypePolyIndexesArg0);
pub struct MyTypePolyArg2Poly<DataStack, StateStack> {
    pub data: DataStack,
    pub state: StateStack,
}
pub struct MyTypePolyArg2PolyArg1Poly<StackHash> {
    pub init: StackHash,
    pub curr: StackHash,
}
pub struct MyTypePolyArg2PolyArg1(pub MyTypePolyArg2PolyArg1Poly<BigInt>);
pub struct MyTypePolyArg2(pub MyTypePolyArg2Poly<BigInt, MyTypePolyArg2PolyArg1>);
"#;
            assert_eq!(gen_type("MyType", &[("MyType", src)]), rust);
        }
    }

    mod toml {
        #[test]
        #[ignore]
        fn serialize() {
            let config = super::super::ConfigBuilder::default().build().unwrap();
            let toml = toml::to_string_pretty(&config).unwrap();
            println!("==========\n{toml}\n========");
        }
    }
}
