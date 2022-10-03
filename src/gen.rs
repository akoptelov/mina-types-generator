use std::collections::{HashMap, HashSet};

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

    /// Rust file preamble.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    preamble: TokenStream,

    /// Type preamble, like attributes.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    type_preamble: TokenStream,

    /// Polymorphic variant preamble.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    poly_var_preamble: TokenStream,

    /// Versioned type, to be used to mark a type with a version.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    versioned_type: TokenStream,

    /// Phantom type, to be used with unused type parameters.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    phantom_type: TokenStream,

    /// Suffix for binable versioned types.
    #[builder(default)]
    #[serde(default)]
    versioned_suffix: Option<String>,

    /// Base types mapping.
    #[builder(default = "base_types()")]
    base_types: HashMap<String, BaseTypeMapping>,

    /// Gids that shouldn't be generated.
    #[builder(default)]
    #[serde(default)]
    skip: HashSet<String>,
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

mod token_stream_opt {
    use proc_macro2::TokenStream;
    use serde::{de::Visitor, Deserializer, Serializer};

    pub fn serialize<S>(ts: &Option<TokenStream>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        if let Some(ts) = ts.as_ref() {
            super::token_stream::serialize(ts, serializer)
        } else {
            serializer.serialize_none()
        }
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Option<TokenStream>, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct V;
        impl<'de> Visitor<'de> for V {
            type Value = Option<TokenStream>;

            fn expecting(&self, formatter: &mut std::fmt::Formatter) -> std::fmt::Result {
                formatter.write_str("Rust token stream")
            }

            fn visit_none<E>(self) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                Ok(None)
            }

            fn visit_some<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                deserializer.deserialize_str(self)
            }

            fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
            where
                E: serde::de::Error,
            {
                v.parse()
                    .map_err(|e| E::custom(format!("lexer error {e}")))
                    .map(Some)
            }
        }

        deserializer.deserialize_option(V)
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
    used_names: HashMap<String, HashSet<&'a Gid>>,

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
#[serde(try_from = "BaseTypeMappingToml", into = "BaseTypeMappingToml")]
pub enum BaseTypeMapping {
    Skip,
    Map(#[serde(with = "token_stream", default)] TokenStream),
    MapWithArg(#[serde(with = "token_stream", default)] TokenStream),
    Table(#[serde(with = "token_stream", default)] TokenStream),
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct BaseTypeMappingToml {
    #[serde(default)]
    skip: Option<bool>,
    #[serde(with = "token_stream_opt", default)]
    rust_id: Option<TokenStream>,
    #[serde(default)]
    args_num: Option<BaseTypeArgs>,
    #[serde(with = "token_stream_opt", default)]
    table: Option<TokenStream>,
}

impl From<BaseTypeMapping> for BaseTypeMappingToml {
    fn from(source: BaseTypeMapping) -> Self {
        match source {
            BaseTypeMapping::Skip => BaseTypeMappingToml {
                skip: Some(true),
                ..Self::default()
            },
            BaseTypeMapping::Map(rust_id) => BaseTypeMappingToml {
                rust_id: Some(rust_id),
                args_num: Some(BaseTypeArgs::None),
                ..Self::default()
            },
            BaseTypeMapping::MapWithArg(rust_id) => BaseTypeMappingToml {
                rust_id: Some(rust_id),
                args_num: Some(BaseTypeArgs::Single),
                ..Self::default()
            },
            BaseTypeMapping::Table(rust_id) => BaseTypeMappingToml {
                table: Some(rust_id),
                ..Self::default()
            },
        }
    }
}

impl TryFrom<BaseTypeMappingToml> for BaseTypeMapping {
    type Error = String;

    fn try_from(source: BaseTypeMappingToml) -> std::result::Result<Self, Self::Error> {
        match (source.rust_id, source.args_num, source.skip, source.table) {
            (Some(rust_id), None, None, None)
            | (Some(rust_id), Some(BaseTypeArgs::None), None, None) => {
                Ok(BaseTypeMapping::Map(rust_id))
            }
            (Some(rust_id), Some(BaseTypeArgs::Single), None, None) => {
                Ok(BaseTypeMapping::MapWithArg(rust_id))
            }
            (None, Some(_), None, None) => Err(format!("Args num without rust_id")),
            (None, None, Some(true), None) => Ok(BaseTypeMapping::Skip),
            (_, _, Some(true), _) => Err(format!("Extra values not allowed for `skip`")),
            (None, None, None, Some(rust_id)) => Ok(BaseTypeMapping::Table(rust_id)),
            (_, _, _, Some(_)) => Err(format!("Extra values not allowed for `table`")),
            _ => Err(format!("Incorrect base type mapping")),
        }
    }
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
            .map(|vid| format_ident!("{}", Self::sanitize_name(vid)));
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
        let base = self.base_type_mapping(&type_name, uuid, &args);
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
                field = Self::sanitize_name(field)
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
        let type_name = format_ident!("{}", Self::sanitize_name(vid));
        let phantom_type = self.config.phantom_type.clone();
        quote! {
            #field_name: #phantom_type< #type_name >
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
        let alt = Self::sanitize_name(alt);
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
        let poly_preamble = self.config.poly_var_preamble.clone();
        let params = self.params(params);
        let constrs = constrs
            .iter()
            .map(|constr| self.generate_poly_constr(type_name, constr));
        quote! {
            #preamble
            #poly_preamble
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
        let Group {
            gid,
            loc: _,
            members,
        } = group;
        let named = !self.xref.is_anonymous(*gid);
        if named {
            if let Some(TypeStatus::Generated(_)) = self.name_mapping.get(gid) {
                return quote!();
            }
        }

        let (tid, (_vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        if let Some(ver_expr) = self.versioned_type(expr) {
            self.generate_versioned_top_app(type_name, named, group, tid, args, ver_expr)
        } else {
            self.generate_plain_top_app(type_name, named, group, tid, args)
        }
    }

    fn get_versioned_type_name(
        name: &str,
        suffix: Option<&str>,
    ) -> std::result::Result<(String, i32), String> {
        if let Some(name) = name.strip_suffix(".t") {
            if let Some((_, version)) = name.rsplit_once(".V") {
                if let Ok(version) = version.parse::<i32>() {
                    return Ok((
                        Self::sanitize_name(&format!("{name}{}", suffix.unwrap_or("Versioned"))),
                        version,
                    ));
                }
            }
        }
        return Err(Self::sanitize_name(&format!("{name}IsNotVersioned")));
    }


    fn generate_versioned_top_app(
        &mut self,
        type_name: Option<&str>,
        named: bool,
        group: &'a Group,
        _tid: &str,
        _args: &'a [Expression],
        ver_expr: &'a Expression,
    ) -> TokenStream {
        let Group { gid, loc, members } = group;
        let (_tid, (vids, _expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        let (type_name, version) = if named {
            let name = some_or_gen_error!(self.group_name(gid), Error::UnknownGroupName(gid));
            Self::get_versioned_type_name(
                name,
                self.config.versioned_suffix.as_ref().map(String::as_str),
            )
            .unwrap_or_else(|e| (e, 1))
        } else {
            (
                some_or_gen_error!(type_name, Error::UnknownGroupName(gid)).to_string(),
                1,
            )
        };

        self.name_mapping
            .insert(gid, TypeStatus::Generated(type_name.clone()));

        let comment = if self.config.generate_comments {
            let comment = self.generate_doc_comment(gid, loc);
            quote! {
                #[doc = #comment]
            }
        } else {
            quote! {}
        };
        let type_ref = self.type_reference(Some(&format!("{type_name}V{version}")), ver_expr);
        let type_name = format_ident!("{type_name}");
        let params = self.params(vids);
        let versioned = self.config.versioned_type.clone();
        quote! {
            #comment
            pub type #type_name #params = #versioned<#type_ref, #version>;
        }
    }

    fn generate_plain_top_app(
        &mut self,
        type_name: Option<&str>,
        named: bool,
        group: &'a Group,
        _tid: &str,
        _args: &'a [Expression],
    ) -> TokenStream {
        let Group { gid, loc, members } = group;
        let (tid, (vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));
        let type_name = if named {
            let name = some_or_gen_error!(self.group_name(gid), Error::UnknownGroupName(gid));
            Self::sanitize_name(name)
        } else {
            some_or_gen_error!(type_name, Error::UnknownGroupName(gid)).to_string()
        };

        self.name_mapping
            .insert(gid, TypeStatus::Generated(type_name.clone()));

        // let venv = ok_or_gen_error!(self.new_venv(&group.gid, vids, args, Some(&type_name)));
        let tenv = self.new_tenv(gid, tid, Some(&type_name));

        let comment = self.generate_doc_comment(gid, loc);
        let expr = if matches!(expr, Expression::Top_app(..)) {
            let type_ref = self.type_reference(Some(&format!("{type_name}Poly")), expr);
            let type_name = format_ident!("{type_name}");
            let preamble = self.config.type_preamble.clone();
            let params = self.params(vids);
            let comment = if self.config.generate_comments {
                quote! {
                    #[doc = #comment]
                }
            } else {
                quote! {}
            };
            quote! {
                #preamble
                #comment
                pub struct #type_name #params (pub #type_ref);
            }
        } else {
            let expr = self.generate_type(Some(&type_name), expr, vids);

            if self.config.skip.contains(&type_name) {
                let comment = format!(" The type `{type_name}` is skipped\n\n{comment}");
                quote! {
                    _comment_!(#comment);
                }
            } else {
                let comment = if self.config.generate_comments {
                    quote! {
                        #[doc = #comment]
                    }
                } else {
                    quote! {}
                };
                quote! {
                    #comment
                    #expr
                }
            }
        };

        self.tenv = tenv;

        expr
    }

    fn versioned_type(&self, expr: &'a Expression) -> Option<&'a Expression> {
        if let Expression::Record(fields) = expr {
            if fields.len() == 2 && &fields[0].0 == "version" && &fields[1].0 == "t" {
                let expr = &fields[1].1;
                if let Expression::Top_app(group, _, args) = expr {
                    if let Some((_, (_, inner_expr))) = group.members.first() {
                        if matches!(inner_expr, Expression::Top_app(inner_group, _, inner_args) if &group.loc == &inner_group.loc && args == inner_args)
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

    fn generate_doc_comment(&self, gid: &Gid, loc: &str) -> String {
        let git_loc = self.git_loc(loc);
        let loc = git_loc.as_ref().map(String::as_str).unwrap_or(loc);
        if let Some(name) = self.xref.for_gid(*gid).and_then(|(_, name)| name) {
            format!(" **Origin**: `{name}`\n\n **Location**: {loc}\n\n **Gid**: {gid}")
        } else {
            format!(" Location: {loc}\n\n Gid: {gid}")
        }
    }

    //              type reference

    pub fn type_reference(&mut self, name_hint: Option<&str>, expr: &'a Expression) -> TokenStream {
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
        self.base_type_mapping(name_hint.unwrap_or("UnknownBaseType"), uuid, &args)
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
            .unwrap_or_else(|| format_ident!("{}", Self::sanitize_name(vid)).to_token_stream())
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
            Box< #type_name < #( #args ),* > >
        }
    }

    fn is_external_type(&self, loc: &Location) -> bool {
        const PREFIXES: &[&str] = &["src/lib/", "src/app"];
        PREFIXES.iter().all(|p| !loc.starts_with(p))
    }

    fn get_gid_name(&self, gid: &Gid) -> Option<(&str, bool)> {
        self.xref.expr_for_gid(*gid).and_then(|(expr, name_opt)| {
            name_opt.map(|name| (name, self.versioned_type(expr).is_some()))
        })
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
                let type_name = if let Some((name, versioned)) = self.get_gid_name(gid) {
                    if versioned {
                        Self::get_versioned_type_name(
                            name,
                            self.config.versioned_suffix.as_ref().map(String::as_str),
                        )
                        .map_or_else(|e| e, |(name, _)| Self::sanitize_name(&name))
                    } else {
                        Self::sanitize_name(name)
                    }
                } else {
                    let mut name = Self::sanitize_name(some_or_gen_error!(
                        self.group_name(gid).or(name_hint),
                        Error::UnknownGroupName(gid)
                    ));
                    if let Some(existing) = self.used_names.get_mut(&name) {
                        //println!("{name}: {existing:?}");
                        if !existing.contains(gid) {
                            name = format!("{name}Dup{}", existing.len());
                            existing.insert(gid);
                        }
                    } else {
                        self.used_names.insert(name.clone(), HashSet::from([gid]));
                    }
                    name
                };
                self.name_mapping
                    .insert(gid, TypeStatus::Pending(type_name.clone()));
                let ts = self.generate_top_app(Some(&type_name), group, loc, args);
                self.add_aux_type(ts);
                self.name_mapping
                    .get(gid)
                    .map(TypeStatus::type_name)
                    .map_or(type_name, String::from)
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

    fn sanitize_name(name: &str) -> String {
        let name = name.strip_suffix(".t").unwrap_or(name);
        let mut san_name = String::new();
        if matches!(name.chars().next(), Some(first) if first.is_numeric()) {
            san_name.push('_');
        }
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
    fn base_type_mapping(
        &mut self,
        type_name: &str,
        uuid: &str,
        args: &'a [Expression],
    ) -> TokenStream {
        if let Some(mapping) = self.config.base_types.get(uuid) {
            match (mapping, args) {
                (BaseTypeMapping::Skip, []) => TokenStream::default(),
                (BaseTypeMapping::Skip, [arg]) => self.type_reference(Some(&type_name), arg),
                (BaseTypeMapping::Skip, _) => {
                    gen_error!("Unexpected number of aguments for the base type {uuid}")
                }
                (BaseTypeMapping::Map(ts), []) => ts.clone(),
                (BaseTypeMapping::Map(_), _) => {
                    gen_error!("Unexpected number of aguments for the base type {uuid}")
                }
                (BaseTypeMapping::MapWithArg(ts), [arg]) => {
                    let ts = ts.clone();
                    let arg = self.type_reference(Some(&format!("{type_name}BaseArg")), arg);
                    quote! { #ts<#arg> }
                }
                (BaseTypeMapping::MapWithArg(_), _) => {
                    gen_error!("Unexpected number of aguments for the base type {uuid}")
                }
                (BaseTypeMapping::Table(rust_id), [arg]) => {
                    let rust_id = rust_id.clone();
                    let args = if let Expression::Top_app(_, _, args) = arg {
                        args
                    } else {
                        return gen_error!("Unexpected argument for table: Top_app expected");
                    };
                    let arg = if let Some((arg, [])) = args.split_first() {
                        arg
                    } else {
                        return gen_error!(
                            "Unexpected argument for table: single Top_app argument expected"
                        );
                    };
                    let elts = if let Expression::Tuple(elts) = arg {
                        elts
                    } else {
                        return gen_error!(
                            "Unexpected argument for table: Tuple expected in Top_app argument"
                        );
                    };
                    let (key, value) = if let [key, value] = &elts[..] {
                        (
                            self.type_reference(Some(&format!("{type_name}Key")), key),
                            self.type_reference(Some(&format!("{type_name}Value")), value),
                        )
                    } else {
                        return gen_error!("Unexpected argument for table: Two-element Tuple expected in Top_app argument");
                    };
                    quote! { #rust_id<#key, #value> }
                }
                (BaseTypeMapping::Table(_), _) => {
                    gen_error!("Unexpected number of aguments for the base type {uuid}")
                }
            }
        } else {
            let name = format_ident!("{}", Self::sanitize_name(uuid));
            if args.is_empty() {
                quote!(#name)
            } else {
                let args = args
                    .iter()
                    .enumerate()
                    .map(|(i, arg)| self.type_reference(Some(&format!("{type_name}Arg{i}")), arg));
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
                BaseTypeMapping::Map (
                    ident.to_token_stream(),
                )
            },
        )
    };
    ($name:ident => $($rust_toks:tt)*) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping::Map (
                stringify!($($rust_toks)*).parse().unwrap(),
            ),
        )
    };
    ($name:ident < _ > => $($rust_toks:tt)*) => {
        (
            String::from(stringify!($name)),
            BaseTypeMapping::MapWithArg (
                stringify!($($rust_toks)*).parse().unwrap(),
            ),
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

    mod names {
        #[test]
        fn versioned_type_name() {
            assert_eq!(
                super::super::Generator::get_versioned_type_name("Mod.Stable.V1.t", None),
                Ok((String::from("ModStableV1Versioned"), 1))
            );
            assert_eq!(
                super::super::Generator::get_versioned_type_name("Mod.Stable.V1", None),
                Err(String::from("ModStableV1IsNotVersioned"))
            );
        }
    }

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
            assert_eq!(gen_ref("(Base foo ())"), "Foo");

            assert_eq!(gen_ref("(Base foo ((Base bar ())))"), "Foo < Bar >");
            assert_eq!(gen_ref("(Base option ((Base bar ())))"), "Option < Bar >");
            assert_eq!(gen_ref("(Base list ((Base bar ())))"), "Vec < Bar >");
            assert_eq!(gen_ref("(Base array ((Base bar ())))"), "Vec < Bar >");
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
