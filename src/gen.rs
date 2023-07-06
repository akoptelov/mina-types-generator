use std::{
    collections::{BTreeMap, HashSet},
    iter, mem,
};

use derive_builder::Builder;
use proc_macro2::{Literal, TokenStream};
use quote::{format_ident, quote, ToTokens};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::xref::XRef;

use super::shape::*;

type Venv<'a> = BTreeMap<&'a str, (TokenStream, usize)>;
type Tenv<'a> = BTreeMap<&'a str, (Context<'a>, &'a [Vid])>;

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

#[allow(unused)]
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
    #[error("Mismatched type parameters lenght for base type `{0}`: expected {1}, got {2}")]
    BaseTypeMismatchTypeParametersLenght(&'a str, usize, usize),
    #[error("Type `{0}` not found")]
    TypeNotFound(String),
    #[error("Unknown base type `{0}`")]
    UnknownBaseType(String),
    #[error("No name for group {0}")]
    UnknownGroupName(&'a Gid),
    #[error("Unresolved type variable {0}")]
    UnresolvedTypeVar(&'a str),
    #[error("Unresolved recursive type reference {0}")]
    UnresolvedRecType(&'a str),
    #[error("Unmatched recursive application arguments for `{0}`")]
    UnmatchedRecAppArgs(&'a str),
    #[error("Cannot extract type version from the name `{0}`")]
    NoVersion(String),
    #[error("Unnamed versioned type, gid {0}")]
    UnnamedVersionedType(&'a Gid),
    #[error("Assertion failed: {0}")]
    Assert(String),
}

impl<'a> From<Error<'a>> for TokenStream {
    fn from(source: Error<'a>) -> Self {
        gen_error!("{source}")
    }
}

impl<'a> From<Error<'a>> for (TokenStream, usize) {
    fn from(source: Error<'a>) -> Self {
        (gen_error!("{source}"), 0)
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

    /// Use newtype pattern when defining types resolved to base type
    #[builder(default)]
    #[serde(default)]
    use_type_alias: bool,

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
    base_types: BTreeMap<String, BaseTypeMapping>,

    /// Gids that shouldn't be generated.
    #[builder(default)]
    #[serde(default)]
    skip: HashSet<String>,

    /// Recursive tuple type.
    ///
    /// Should be a generic type with two parameters, inner type and an integer
    /// depth.
    #[builder(default)]
    #[serde(with = "token_stream", default)]
    rec_tuple_type: TokenStream,

    /// OCaml module name mapping.
    ///
    /// Can be used to e.g. completely remove some module from hierarchy, like
    /// `Make_str`.
    #[builder(default)]
    #[serde(default)]
    ocaml_mod_mapping: BTreeMap<String, String>,

    /// Reference mapping.
    ///
    /// If manual type built over a generated type should be used, a pair of
    /// (original OCaml name, manual Rust name) should be included into this
    /// mapping.
    #[builder(default)]
    #[serde(default)]
    rust_ref_mapping: BTreeMap<String, String>,
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct TypeId<'a> {
    gid_or_name: GidOrName<'a>,
    arg_refs: String,
}

impl<'a> std::fmt::Display for TypeId<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.gid_or_name {
            GidOrName::Gid(gid) => write!(f, "Gid({gid})"),
            GidOrName::Name(name) => write!(f, "{name}"),
        }?;
        write!(f, "<{}>", self.arg_refs)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, derive_more::From)]
enum GidOrName<'a> {
    Gid(&'a Gid),
    Name(String),
}

impl<'a> TypeId<'a> {
    fn for_gid(gid: &'a Gid) -> Self {
        TypeId {
            gid_or_name: gid.into(),
            arg_refs: String::new(),
        }
    }

    fn for_gid_with_args(gid: &'a Gid, arg_refs: String) -> Self {
        TypeId {
            gid_or_name: gid.into(),
            arg_refs,
        }
    }

    fn for_name(name: impl Into<String>, arg_refs: String) -> Self {
        TypeId {
            gid_or_name: name.into().into(),
            arg_refs,
        }
    }
}

#[derive(Debug)]
struct GeneratedType<'a> {
    ctx: Context<'a>,
    type_ref: TokenStream,
    type_def: TokenStream,
    size: usize,
}

impl<'a> GeneratedType<'a> {
    fn new(ctx: &Context<'a>, type_ref: TokenStream, type_def: TokenStream, size: usize) -> Self {
        Self {
            ctx: ctx.clone(),
            type_ref,
            type_def,
            size,
        }
    }
}

pub struct Generator<'a> {
    /// Type expression name/id information.
    xref: &'a XRef<'a>,

    /// Generator configuration.
    config: Config,

    /// Group to type name mapping.
    name_mapping: BTreeMap<TypeId<'a>, GeneratedType<'a>>,

    /// Types explicitly requested to be generated.
    requested_types: Vec<TypeId<'a>>,

    /// Type variables substitution.
    venv: Venv<'a>,
    /// Types substitution (for recursive types).
    tenv: Tenv<'a>,

    /// Name conversion rules.
    name_conv: NameMapper,
}

#[derive(Clone, Debug)]
struct TopAppContext<'a> {
    gid: &'a Gid,
    arg_refs: String,
    loc: &'a str,
}

#[derive(Clone, Debug)]
pub struct Context<'a> {
    name: String,
    is_mandatory: bool,
    top_apps: Vec<TopAppContext<'a>>,
}

impl<'a> Default for Context<'a> {
    fn default() -> Self {
        Self {
            name: String::from("empty"),
            is_mandatory: Default::default(),
            top_apps: Default::default(),
        }
    }
}

#[derive(Debug)]
struct NameMapper {
    /// OCaml module name mapping.
    ocaml_mod_mapping: BTreeMap<String, String>,
    ///
    /// Rust reference mapping.
    rust_ref_mapping: BTreeMap<String, String>,
}

impl NameMapper {
    fn new<M1: Into<BTreeMap<String, String>>, M2: Into<BTreeMap<String, String>>>(
        ocaml_mod_mapping: M1,
        rust_ref_mapping: M2,
    ) -> Self {
        NameMapper {
            ocaml_mod_mapping: ocaml_mod_mapping.into(),
            rust_ref_mapping: rust_ref_mapping.into(),
        }
    }

    fn map_ocaml_mod<'a>(&'a self, name: &'a str) -> &'a str {
        self.ocaml_mod_mapping
            .get(name)
            .map_or(name, String::as_str)
    }

    fn map_rust_ref<'a>(&'a self, name: &'a str) -> Option<&'a str> {
        self.rust_ref_mapping.get(name).map(String::as_str)
    }
}

impl<'a> Context<'a> {
    fn with_name_or_inherited(
        &self,
        name: Option<&'a str>,
        gid: &'a Gid,
        arg_refs: String,
        loc: &'a str,
    ) -> Self {
        let value = TopAppContext { gid, arg_refs, loc };
        if let Some(name) = name {
            let name = name.strip_suffix(".t").unwrap_or(name);
            Self {
                name: name.into(),
                is_mandatory: true,
                top_apps: vec![value.clone()],
            }
        } else {
            let mut top_apps = self.top_apps.clone();
            top_apps.push(value.clone());
            Self {
                name: self.name.clone(),
                is_mandatory: self.is_mandatory,
                top_apps,
            }
        }
    }

    fn is_mandatory(&self) -> bool {
        self.is_mandatory
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn gid(&self) -> Option<&'a Gid> {
        self.top_apps.first().map(|ta| ta.gid)
    }

    fn arg_refs(&self) -> &str {
        self.top_apps
            .first()
            .map_or("", |ta| &ta.arg_refs)
    }

    fn derive(&self, suffix: &str) -> Self {
        Self {
            name: format!("{name}.{suffix}", name = self.name),
            is_mandatory: false,
            top_apps: Vec::new(),
        }
    }

    fn sanitize_name(name: &str, mapper: &NameMapper) -> String {
        name.split('.')
            .map(|comp| mapper.map_ocaml_mod(comp))
            .map(Generator::name_for_type)
            .collect::<Vec<_>>()
            .join("")
    }

    /// Type name for the context.
    ///
    /// Name is generated from OCaml name using OCaml module mapping.
    fn type_name(&self, mapper: &NameMapper) -> TokenStream {
        let name = Self::sanitize_name(&self.name, mapper);
        format_ident!("{name}").to_token_stream()
    }

    /// Reference to the type defined by the context.
    ///
    /// Name is eigher taken from Rust reference mapping or generated from OCaml
    /// name using OCaml module mapping.
    fn type_ref(&self, mapper: &NameMapper) -> TokenStream {
        let name = mapper
            .map_rust_ref(&self.name)
            .map_or_else(|| Self::sanitize_name(&self.name, mapper), String::from);
        format_ident!("{name}").to_token_stream()
    }

    fn mandatory_name_matches(&self, type_ref: &TokenStream, mapper: &NameMapper) -> bool {
        !self.is_mandatory || self.type_ref(mapper).to_string() == type_ref.to_string()
    }
}

impl<'a> std::fmt::Display for Context<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.name())
    }
}

impl<'a> PartialEq<TokenStream> for Context<'a> {
    fn eq(&self, other: &TokenStream) -> bool {
        self.name() == &other.to_string()
    }
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
    Map(#[serde(with = "token_stream", default)] TokenStream),
    MapWithArg(#[serde(with = "token_stream", default)] TokenStream),
    Table(#[serde(with = "token_stream", default)] TokenStream),
}

#[derive(Debug, Default, Serialize, Deserialize)]
struct BaseTypeMappingToml {
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
        match (source.rust_id, source.args_num, source.table) {
            (Some(rust_id), None, None) | (Some(rust_id), Some(BaseTypeArgs::None), None) => {
                Ok(BaseTypeMapping::Map(rust_id))
            }
            (Some(rust_id), Some(BaseTypeArgs::Single), None) => {
                Ok(BaseTypeMapping::MapWithArg(rust_id))
            }
            (None, Some(_), None) => Err(format!("Args num without rust_id")),
            (None, None, Some(rust_id)) => Ok(BaseTypeMapping::Table(rust_id)),
            (_, _, Some(_)) => Err(format!("Extra values not allowed for `table`")),
            _ => Err(format!("Incorrect base type mapping")),
        }
    }
}

impl<'a> Generator<'a> {
    pub fn new(xref: &'a XRef<'a>, mut config: Config) -> Self {
        Self {
            xref,
            name_conv: NameMapper::new(
                mem::take(&mut config.ocaml_mod_mapping),
                mem::take(&mut config.rust_ref_mapping),
            ),
            config,
            name_mapping: BTreeMap::new(),
            requested_types: Vec::new(),
            venv: BTreeMap::new(),
            tenv: BTreeMap::new(),
        }
    }

    pub fn generate_all(&mut self) -> TokenStream {
        for name in self.xref.names() {
            ok_or_gen_error!(self.generate_for_name(name));
        }
        self.generated_to_token_stream()
    }

    pub fn generate_types<T, I>(&mut self, types: I) -> TokenStream
    where
        T: 'a + AsRef<str>,
        I: IntoIterator<Item = T>,
    {
        for name in types {
            ok_or_gen_error!(self.generate_for_name(name.as_ref()));
        }
        self.generated_to_token_stream()
    }

    pub fn generate(&mut self, name: &str) -> TokenStream {
        ok_or_gen_error!(self.generate_for_name(name));
        self.generated_to_token_stream()
    }

    fn git_loc(&self, loc: &str) -> Option<String> {
        let prefix = self.config.git_prefix.as_ref()?;
        let mut it = loc.split(':');
        let file = it.next()?;
        let line = it.next()?;
        Some(format!("[{loc}]({prefix}{file}#L{line})",))
    }

    fn generate_doc_comment(&self, ctx: &Context<'a>) -> String {
        let mut comment = if ctx.is_mandatory {
            format!(" **OCaml name**: `{}`", ctx.name())
        } else {
            format!(" Derived name: `{}`", ctx.name())
        };
        for TopAppContext { gid, arg_refs, loc } in &ctx.top_apps {
            let git_loc = self.git_loc(loc);
            let loc = git_loc.as_ref().map(|loc| loc.as_str()).unwrap_or(*loc);
            comment += &format!(
                r#"

 Gid: `{gid}`
 Location: {loc}
"#
            );
            if !arg_refs.is_empty() {
                comment += &format!(
                    r#" Args: {arg_refs}
"#
                );
            }
        }
        comment
    }

    fn generated_to_token_stream(&mut self) -> TokenStream {
        let mut generated = mem::take(&mut self.name_mapping);
        let requested = mem::take(&mut self.requested_types)
            .into_iter()
            .filter_map(|type_id| generated.remove(&type_id))
            .collect::<Vec<_>>();
        let mut ts = self.config.preamble.clone();
        requested
            .into_iter()
            .chain(generated.into_values())
            .for_each(|g| {
                if self.config.blank_lines {
                    ts.extend(quote! {_blank_!();});
                }
                if self.config.generate_comments {
                    let comment = self.generate_doc_comment(&g.ctx);
                    ts.extend(quote! {
                        #[doc = #comment]
                    })
                }
                ts.extend(g.type_def);
            });
        ts
    }

    fn generate_for_name(&mut self, name: &str) -> Result<TokenStream> {
        match self.xref.expr_for_name(name) {
            Some(expr @ Expression::Top_app(Group { gid, .. }, _, _args)) => {
                self.requested_types.push(TypeId::for_gid(gid));
                Ok(self.generate_type(Context::default(), expr).0)
            }
            Some(expr) => Err(Error::Assert(format!(
                "Unexpected top-level type: {expr:?}"
            ))),
            None => Err(Error::TypeNotFound(name.to_string())),
        }
    }

    #[allow(dead_code)]
    fn generate_type_defs(&mut self, expr: &'a Expression) -> TokenStream {
        self.generate_type(Context::default(), expr);
        self.generated_to_token_stream()
    }

    /// Registers the generated type as corresponding to group id `gid`.
    fn register_type(
        &mut self,
        ctx: &Context<'a>,
        type_ref: TokenStream,
        type_def: TokenStream,
        size: usize,
    ) -> (TokenStream, usize) {
        let type_id = ctx.gid().map_or_else(
            || TypeId::for_name(ctx.name(), ctx.arg_refs().to_string()),
            |gid| TypeId::for_gid_with_args(gid, ctx.arg_refs().to_string()),
        );
        let type_desc = GeneratedType::new(ctx, type_ref.clone(), type_def, size);
        if let Some(prev) = self.name_mapping.insert(type_id.clone(), type_desc) {
            gen_error!(
                "duplicate type registered for {type_id} as {type_ref}, already registered as {prev}",
                prev = prev.type_ref,
            );
        }
        (type_ref, size)
    }

    fn register_skipped_type(&self, ctx: &Context<'a>) -> (TokenStream, usize) {
        (ctx.type_ref(&self.name_conv), 1)
    }

    pub fn generate_type(
        &mut self,
        ctx: Context<'a>,
        expr: &'a Expression,
    ) -> (TokenStream, usize) {
        match expr {
            Expression::Annotate(_, _) => todo!(),
            Expression::Base(uuid, args) => self.base_type(ctx, uuid, args),
            Expression::Record(exprs) => self.record(ctx, exprs),
            Expression::Variant(alts) => self.variant(ctx, alts),
            Expression::Tuple(exprs) => self.tuple(ctx, exprs),
            Expression::Poly_variant((loc, constrs)) => self.poly_variant(ctx, loc, constrs),
            Expression::Var((loc, vid)) => self.var(loc, vid),
            Expression::Rec_app(tid, args) => self.rec_app(tid, args),
            Expression::Top_app(group, tid, args) => self.top_app(ctx, group, tid, args),
        }
    }

    fn base_type(
        &mut self,
        ctx: Context<'a>,
        uuid: &str,
        args: &'a [Expression],
    ) -> (TokenStream, usize) {
        match (self.config.base_types.get(uuid).cloned(), args) {
            (None, _) => Error::UnknownBaseType(uuid.into()).into(),
            (Some(BaseTypeMapping::Map(mapped)), []) => (quote! { #mapped }, 1),
            (Some(BaseTypeMapping::Map(_)), _) => {
                Error::BaseTypeMismatchTypeParametersLenght(uuid, 0, args.len()).into()
            }
            (Some(BaseTypeMapping::MapWithArg(mapped)), [arg]) => {
                let (arg, _) = self.generate_type(ctx.derive("Arg"), arg);
                (quote! { #mapped < #arg > }, 1)
            }
            (Some(BaseTypeMapping::MapWithArg(_)), args) => {
                Error::BaseTypeMismatchTypeParametersLenght(uuid, 0, args.len()).into()
            }
            (Some(BaseTypeMapping::Table(_rust_id)), [_arg]) => {
                todo!()
                // let rust_id = rust_id.clone();
                // let args = if let Expression::Top_app(_, _, args) = arg {
                //     args
                // } else {
                //     return gen_error!("Unexpected argument for table: Top_app expected");
                // };
                // let arg = if let Some((arg, [])) = args.split_first() {
                //     arg
                // } else {
                //     return gen_error!(
                //         "Unexpected argument for table: single Top_app argument expected"
                //     );
                // };
                // let elts = if let Expression::Tuple(elts) = arg {
                //     elts
                // } else {
                //     return gen_error!(
                //         "Unexpected argument for table: Tuple expected in Top_app argument"
                //     );
                // };
                // let (key, value) = if let [key, value] = &elts[..] {
                //     (
                //         self.type_reference(Some(&format!("{type_name}Key")), key),
                //         self.type_reference(Some(&format!("{type_name}Value")), value),
                //     )
                // } else {
                //     return gen_error!("Unexpected argument for table: Two-element Tuple expected in Top_app argument");
                // };
                // quote! { #rust_id<#key, #value> }
            }
            (Some(BaseTypeMapping::Table(_)), _) => (
                gen_error!("Unexpected number of aguments for the base type {uuid}"),
                0,
            ),
        }
    }

    fn record(
        &mut self,
        ctx: Context<'a>,
        fields: &'a [(String, Expression)],
    ) -> (TokenStream, usize) {
        let name = ctx.type_name(&self.name_conv);
        let preamble = self.config.type_preamble.clone();
        let phantom_fields = self.get_unused_params(fields.iter().map(|(_, expr)| expr));
        let phantom_fields = phantom_fields
            .iter()
            .enumerate()
            .map(|(i, vid)| self.phantom_field(i, vid))
            .collect::<Vec<_>>();
        let (fields, sizes): (Vec<_>, Vec<_>) = fields
            .iter()
            .map(|(field, expr)| self.field(&ctx, field, expr, true))
            .unzip();

        let size = sizes.iter().sum();
        let fields = fields.into_iter().chain(phantom_fields);

        let type_def = quote! {
            #preamble
            pub struct #name {
                #(#fields,)*
            }
        };
        self.register_type(&ctx, ctx.type_ref(&self.name_conv), type_def, size)
    }

    fn get_unused_params<I: Clone + IntoIterator<Item = &'a Expression>>(
        &self,
        _exprs: I,
    ) -> Vec<&'a Vid> {
        Vec::new()
        // params
        //     .iter()
        //     .filter(|vid| !self.is_used(vid, exprs.clone()))
        //     .collect()
    }

    #[allow(dead_code)]
    fn is_used<I: IntoIterator<Item = &'a Expression>>(&self, vid: &'a Vid, exprs: I) -> bool {
        exprs.into_iter().any(|expr| self.is_used_in(vid, expr))
    }

    #[allow(dead_code)]
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

    fn field(
        &mut self,
        ctx: &Context<'a>,
        field: &str,
        expr: &'a Expression,
        make_public: bool,
    ) -> (TokenStream, usize) {
        let field_name = Self::field_ident(field);
        let (field_type, size) = self.generate_type(ctx.derive(field), expr);
        let p = if make_public { quote!(pub) } else { quote!() };
        (
            quote! {
                #p #field_name: #field_type
            },
            size,
        )
    }

    fn phantom_field(&self, _i: usize, _vid: &Vid) -> TokenStream {
        todo!()
        // let field_name = format_ident!("_phantom_data_{}", i.to_string());
        // let type_name = Self::type_ident(vid);
        // let phantom_type = self.config.phantom_type.clone();
        // quote! {
        //     #field_name: #phantom_type< #type_name >
        // }
    }

    fn should_box_alt(&self, size: usize, min_size: usize) -> bool {
        if min_size == 0 {
            size > 1
        } else {
            size > min_size * 3
        }
    }

    fn variant(
        &mut self,
        ctx: Context<'a>,
        alts: &'a [(String, Vec<Expression>)],
    ) -> (TokenStream, usize) {
        let name = ctx.type_name(&self.name_conv);
        let preamble = self.config.type_preamble.clone();
        let (alt_types, sizes): (Vec<_>, Vec<_>) = alts
            .iter()
            .map(|(alt, exprs)| {
                let ctx = ctx.derive(alt);
                if exprs.is_empty() {
                    ((alt, Vec::new(), false), 1)
                } else if let Some((Expression::Record(fields), [])) = exprs.split_first() {
                    let (fields, sizes): (Vec<_>, Vec<_>) = fields
                        .iter()
                        .map(|(name, expr)| self.field(&ctx, name, expr, false))
                        .unzip();
                    ((alt, fields, true), sizes.into_iter().sum())
                } else {
                    let it = exprs.iter().enumerate();
                    let (items, sizes): (Vec<_>, Vec<_>) = if exprs.len() == 1 {
                        it.map(|(_, expr)| self.generate_type(ctx.clone(), expr))
                            .unzip()
                    } else {
                        it.map(|(i, expr)| self.generate_type(ctx.derive(&i.to_string()), expr))
                            .unzip()
                    };
                    ((alt, items, false), sizes.into_iter().sum())
                }
            })
            .unzip();
        let min_size = sizes.iter().min().cloned().unwrap_or(1);
        let (alts, sizes): (Vec<_>, Vec<_>) = iter::zip(alt_types, sizes)
            .map(|((alt, items, is_rec), size)| {
                self.alternative(alt, &items, is_rec, size, min_size)
            })
            .unzip();
        let max_size = sizes.into_iter().max().unwrap_or(1);
        let type_def = quote! {
            #preamble
            pub enum #name {
                #(
                    #alts,
                )*
            }
        };
        self.register_type(&ctx, name, type_def, max_size)
    }

    fn alternative(
        &mut self,
        alt: &str,
        items: &[TokenStream],
        is_rec: bool,
        size: usize,
        min_size: usize,
    ) -> (TokenStream, usize) {
        let alt_name = Self::type_ident(alt);
        if items.is_empty() {
            (quote!(#alt_name), 1)
        } else if is_rec {
            // TODO generate intermediate type for the record?
            (
                quote! {
                    #alt_name {
                        #(#items,)*
                    }
                },
                size,
            )
        } else if self.should_box_alt(size, min_size) {
            let items = if items.len() == 1 {
                quote! { Box<#(#items),*> }
            } else {
                quote! { Box<(#(#items,)*)> }
            };
            (
                quote! {
                    #alt_name(#items)
                },
                1,
            )
        } else {
            (
                quote! {
                    #alt_name(#(#items,)*)
                },
                size,
            )
        }
    }

    fn is_unit(expr: &Expression) -> bool {
        matches!(expr, Expression::Base(_, exprs) if exprs.is_empty())
    }

    /// Checks whether this expression is a recursive tuple.
    ///
    /// Recursive tuples like `(A, (A, (A, ..., () ...)))` are widely used in
    /// OCaml code, and are hard to handle in Rust if represented literaly.
    /// Instead, they can be represented as e.g. fixed length arrays.
    ///
    /// This function detects if this is such a recursive tuple, and returns
    /// base type `A` and the recursion depth.
    fn is_recursive_tuple(exprs: &'a [Expression]) -> Option<(&'a Expression, usize)> {
        match Self::is_recursive_tuple_(exprs) {
            Some((expr, depth)) if depth > 1 => Some((expr, depth)),
            _ => None,
        }
    }
    fn is_recursive_tuple_(exprs: &'a [Expression]) -> Option<(&'a Expression, usize)> {
        match exprs {
            [l, r] if Self::is_unit(r) => Some((l, 1)),
            [l, Expression::Tuple(s)] => {
                Self::is_recursive_tuple_(s).and_then(
                    |(a, d)| {
                        if l == a {
                            Some((a, d + 1))
                        } else {
                            None
                        }
                    },
                )
            }
            _ => None,
        }
    }

    fn tuple(&mut self, ctx: Context<'a>, exprs: &'a [Expression]) -> (TokenStream, usize) {
        let preamble = self.config.type_preamble.clone();
        if !self.config.rec_tuple_type.is_empty() {
            let rec_tuple_type = self.config.rec_tuple_type.clone();
            if let Some((expr, depth)) = Self::is_recursive_tuple(exprs) {
                let (expr, size) = self.generate_type(ctx.derive("0"), expr);
                let size = size * depth;
                let depth = Literal::usize_unsuffixed(depth);
                return (quote!(#rec_tuple_type<#expr, #depth>), size);
            }
        }
        let (exprs_, sizes): (Vec<_>, Vec<_>) = exprs
            .iter()
            .enumerate()
            .map(|(i, expr)| self.generate_type(ctx.derive(&i.to_string()), expr))
            .unzip();
        let size = sizes.into_iter().sum();

        if ctx.is_mandatory() {
            let name = ctx.type_name(&self.name_conv);
            // we should generate the type corresponding to this name
            let type_def = quote! {
                #preamble
                pub struct #name (#(pub #exprs_,)*);
            };
            self.register_type(&ctx, name, type_def, size)
        } else {
            (
                quote! {

                    (#(#exprs_,)*)
                },
                size,
            )
        }
    }

    fn poly_variant(
        &mut self,
        ctx: Context<'a>,
        _loc: &Location,
        constrs: &'a [PolyConstr],
    ) -> (TokenStream, usize) {
        let name = ctx.type_name(&self.name_conv);
        let preamble = self.config.type_preamble.clone();
        let poly_preamble = self.config.poly_var_preamble.clone();
        let (constrs, sizes): (Vec<_>, Vec<_>) = constrs
            .iter()
            .map(|constr| self.poly_constr(&ctx, constr))
            .unzip();
        let min_size = sizes.iter().min().cloned().unwrap_or_default();
        let (constrs, sizes): (Vec<_>, Vec<_>) = iter::zip(constrs, sizes)
            .map(|((name, constr), size)| {
                let name = Self::poly_variant_ident(name);
                if constr.is_none() {
                    (
                        quote! {
                            #[allow(non_camel_case_types)]
                            #name
                        },
                        0,
                    )
                } else if self.should_box_alt(size, min_size) {
                    (
                        quote! {
                            #[allow(non_camel_case_types)]
                            #name(Box<#constr>)
                        },
                        1,
                    )
                } else {
                    (
                        quote! {
                            #[allow(non_camel_case_types)]
                            #name(#constr)
                        },
                        size,
                    )
                }
            })
            .unzip();
        let type_def = quote! {
            #preamble
            #poly_preamble
            pub enum #name {
                #(#constrs,)*
            }
        };
        self.register_type(
            &ctx,
            name,
            type_def,
            sizes.into_iter().max().unwrap_or_default(),
        )
    }

    fn poly_constr(
        &mut self,
        ctx: &Context<'a>,
        constr: &'a PolyConstr,
    ) -> ((&'a str, Option<TokenStream>), usize) {
        match constr {
            PolyConstr::Constr((name, opt_expr)) => {
                if let Some(expr) = opt_expr {
                    let (expr, size) = self.generate_type(ctx.derive(name), expr);
                    ((name, Some(expr)), size)
                } else {
                    ((name, None), 0)
                }
            }
            PolyConstr::Inherit(_) => (
                (
                    "",
                    Some(Error::Assert(format!("poly constr inherit is not implemented")).into()),
                ),
                0,
            ),
        }
    }

    fn var(&self, _loc: &str, vid: &str) -> (TokenStream, usize) {
        some_or_gen_error!(self.venv.get(vid).cloned(), Error::UnresolvedTypeVar(vid))
    }

    fn rec_app(&mut self, tid: &str, args: &[Expression]) -> (TokenStream, usize) {
        let (ctx, vids) = some_or_gen_error!(self.tenv.get(tid), Error::UnresolvedRecType(tid));
        if vids.len() != args.len() {
            return Error::UnmatchedRecAppArgs(tid).into();
        }
        if iter::zip(*vids, args)
            .any(|(vid, arg)| matches!(arg, Expression::Var((_, v)) if v == vid))
        {
            let name = ctx.type_ref(&self.name_conv);
            (
                quote! {
                    Box<#name>
                },
                1,
            )
        } else {
            Error::UnmatchedRecAppArgs(tid).into()
        }
    }

    fn stringify_arg_refs<'z, I: 'z + Iterator<Item = &'z TokenStream>>(arg_refs: I) -> String {
        quote! {
            #(#arg_refs),*
        }
        .to_string()
    }

    fn top_app(
        &mut self,
        ctx: Context<'a>,
        group: &'a Group,
        tid: &'a str,
        args: &'a [Expression],
    ) -> (TokenStream, usize) {
        let Group { gid, loc, members } = group;

        let (_tid, (vids, expr)) = some_or_gen_error!(members.first(), Error::EmptyGroup(&gid));

        if vids.len() != args.len() {
            return Error::MismatchTypeParametersLenght(gid, vids.len(), args.len()).into();
        }

        if let Some(_ver_expr) = self.versioned_type(expr) {
            let (type_ref, size) = self.generate_type(ctx, expr);
            // TODO
            (
                quote! {
                    Versioned<#type_ref, 1>
                },
                size,
            )
        } else {
            let arg_refs = self.substitute_args(&ctx, vids, args);
            let arg_refs_str = Self::stringify_arg_refs(arg_refs.iter().map(|(ar, _)| ar));
            let type_id = TypeId::for_gid_with_args(gid, arg_refs_str.clone());
            if let Some(gen_type) = self.name_mapping.get(&type_id) {
                return (gen_type.type_ref.clone(), gen_type.size);
            }

            let venv = self.new_venv(vids, &arg_refs);
            let tenv = self.new_tenv(tid, &ctx, vids);

            let ctx = ctx.with_name_or_inherited(self.global_name(gid), gid, arg_refs_str, loc);

            // check if to skip the type
            if self
                .config
                .skip
                .contains(&ctx.type_name(&self.name_conv).to_string())
            {
                return self.register_skipped_type(&ctx);
            }

            let (type_ref, size) = self.generate_type(ctx.clone(), expr);

            self.tenv = tenv;
            self.venv = venv;

            if ctx.mandatory_name_matches(&type_ref, &self.name_conv) {
                // underlying type has the same name as this one
                return (type_ref, size);
            }

            let name = ctx.type_name(&self.name_conv);
            let type_def = if self.config.use_type_alias {
                quote! {
                    pub type #name = #type_ref;
                }
            } else {
                let preamble = &self.config.type_preamble;
                quote! {
                    #preamble
                    pub struct #name(pub #type_ref);
                }
            };
            self.register_type(&ctx, ctx.type_ref(&self.name_conv), type_def, size)
        }
    }

    fn global_name(&self, gid: &'a Gid) -> Option<&'a str> {
        self.xref
            .expr_for_gid(*gid)
            .and_then(|(_, name_opt)| name_opt)
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

    fn new_venv(&mut self, vids: &'a [String], arg_refs: &[(TokenStream, usize)]) -> Venv<'a> {
        let mut venv = self.venv.clone();
        venv.extend(
            iter::zip(vids, arg_refs).map(|(vid, arg_ref)| (vid.as_str(), arg_ref.clone())),
        );

        std::mem::replace(&mut self.venv, venv)
    }

    fn new_tenv(&mut self, tid: &'a str, ctx: &Context<'a>, vids: &'a [Vid]) -> Tenv<'a> {
        let mut tenv = self.tenv.clone();
        tenv.insert(tid, (ctx.clone(), vids));
        std::mem::replace(&mut self.tenv, tenv)
    }

    fn field_ident(name: &str) -> TokenStream {
        debug_assert!(name.chars().all(|ch| ch == '_' || ch.is_alphanumeric()));
        format_ident!("{name}").to_token_stream()
    }

    fn name_for_type(name: &str) -> String {
        name.chars()
            .scan(true, |upcase, ch| {
                if !ch.is_alphanumeric() {
                    *upcase = true;
                    Some(None)
                } else if *upcase {
                    *upcase = false;
                    Some(Some(ch.to_ascii_uppercase()))
                } else {
                    Some(Some(ch))
                }
            })
            .filter_map(|it| it)
            .collect::<String>()
    }

    fn name_for_type_no_conv(name: &str) -> String {
        name.chars()
            .filter(|ch| *ch == '_' || ch.is_alphanumeric())
            .collect::<String>()
    }

    /// Sanitizes OCaml ident as a Rust type name.
    fn type_ident(name: &str) -> TokenStream {
        let ident = Generator::name_for_type(name);
        format_ident!("{ident}").to_token_stream()
    }

    /// Sanitizes OCaml ident as a Rust type name.
    fn poly_variant_ident(name: &str) -> TokenStream {
        let ident = Generator::name_for_type_no_conv(name);
        format_ident!("{ident}").to_token_stream()
    }

    // fn group_name(&self, gid: &Gid) -> Option<&str> {
    //     self.xref
    //         .for_gid(*gid)
    //         .and_then(|(_, name)| name)
    //         .or_else(|| self.name_mapping.get(gid).map(String::as_str))
    // }

    fn substitute_args(
        &mut self,
        ctx: &Context<'a>,
        vids: &'a [Vid],
        args: &'a [Expression],
    ) -> Vec<(TokenStream, usize)> {
        iter::zip(vids, args)
            .map(|(vid, expr)| self.generate_type(ctx.derive(vid), expr))
            .collect()
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

fn base_types() -> BTreeMap<String, BaseTypeMapping> {
    BTreeMap::from([
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

#[macro_export]
macro_rules! base {
    ($uuid:expr) => {
        Expression::Base($uuid.into(), Vec::new())
    };
    ($uuid:expr, $arg:expr) => {
        Expression::Base($uuid.into(), vec![$arg.clone()])
    };
    ($uuid:ident) => {
        Expression::Base(stringify!($uuid).into(), Vec::new())
    };
    ($uuid:ident, $arg:expr) => {
        Expression::Base(stringify!($uuid).into(), vec![$arg.clone()])
    };
}

#[macro_export]
macro_rules! top_app {
    ($gid:expr, $expr:expr) => {
        crate::shape::Expression::Top_app(
            crate::shape::Group {
                gid: $gid,
                loc: String::new(),
                members: vec![(String::from("t"), (vec![], $expr.clone()))],
            },
            String::from("t"),
            Vec::new(),
        )
    };
    ($gid:expr, $expr:expr, $($vid:ident => $arg:expr),* $(,)?) => {
        crate::shape::Expression::Top_app(
            crate::shape::Group {
                gid: $gid,
                loc: String::new(),
                members: vec![(String::from("t"), (vec![$(stringify!($vid).into()),*], $expr))],
            },
            String::from("t"),
            vec![$($arg.clone()),*],
        )
    };
}

#[macro_export]
macro_rules! record {
    ($($arg:ident: $ty:expr),* $(,)?) => {
        crate::shape::Expression::Record(
            vec![
                $( (stringify!($arg).into(), $ty.clone()) ),*
            ]
        )
    };
}

#[macro_export]
macro_rules! tuple {
    ($($item:expr),* $(,)?) => {
        crate::shape::Expression::Tuple(vec![$($item.clone()),*])
    };
}

#[macro_export]
macro_rules! variant {
    ($(
        $alt:ident $(($($item:expr),+ $(,)?))?
    ),* $(,)?) => {
        Expression::Variant(vec![$(
            (String::from(stringify!($alt)), vec![$($($item.clone()),+)?])
        ),*])
    };
    ($(
        $alt:ident { $($field:ident : $item:expr),* $(,)? }
    ),* $(,)?) => {
        Expression::Variant(vec![$(
            (String::from(stringify!($alt)), vec![
                Expression::Record(vec![
                    $( (stringify!($field).into(), $item.clone()) ),*
                ])
            ])
        ),*])
    };
}

#[macro_export]
macro_rules! var {
    ($var:ident) => {
        var!(stringify!($var))
    };
    ($var:expr) => {
        crate::shape::Expression::Var((String::new(), $var.into()))
    };
}

#[cfg(test)]
mod tests;
