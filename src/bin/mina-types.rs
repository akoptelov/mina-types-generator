use std::{
    cmp::Ordering,
    fs::{self, File},
    io::{BufRead, BufReader, Read, Write},
    path::{Path, PathBuf},
};

use anyhow::{bail, format_err, Result};
use bin_prot_rs::{
    doc::Doc,
    shape::{Expression, Group, PolyConstr},
    visit::{Visiting, Visitor},
    xref::{NamedShape, XRef},
};
use clap::{ArgEnum, Args, Parser, Subcommand};
use rsexp::SexpOf;
use rust_format::{Formatter, RustFmt};

#[derive(Parser, Debug)]
struct Cli {
    #[clap(value_parser)]
    file: String,

    #[clap(short, long)]
    no_eval: bool,

    #[clap(subcommand)]
    command: Commands,
}

#[derive(Args, Debug)]
struct Gen {
    #[clap(short, long)]
    config: Option<PathBuf>,

    #[clap(short, long)]
    out: Option<PathBuf>,

    #[clap(short, long)]
    all: bool,

    #[clap(value_parser)]
    types: Vec<String>,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Filter {
        #[clap(short, long)]
        depth: Option<usize>,
        #[clap(arg_enum, short, long)]
        enable: Vec<ExprKind>,
    },
    Doc {
        #[clap(short, long)]
        _type: Vec<String>,
        #[clap(short, long)]
        all: bool,
    },
    Gen(Gen),
    Dump(Dump),
}

#[derive(Args, Debug)]
struct Dump {
    #[clap(short, long)]
    _type: Vec<String>,
    #[clap(short, long)]
    dir: Option<PathBuf>,
}

impl Dump {
    fn run(self, shapes: Vec<Type>) -> Result<()> {
        let dir = self.dir.unwrap_or_default();
        if !dir.exists() {
            fs::create_dir_all(&dir)?;
        } else if !dir.is_dir() {
            bail!("{dir:?} is not a directory");
        }
        let xref = XRef::new(&shapes)?;
        for name in self._type {
            let expr = xref
                .expr_for_name(&name)
                .ok_or(anyhow::format_err!("no expr for {name}"))?;
            Self::dump(&xref, expr, &dir)?;
        }
        Ok(())
    }

    fn dump(xref: &XRef, expr: &Expression, dir: &Path) -> Result<()> {
        let map = |expr| Self::dump(xref, expr, dir);
        match expr {
            Expression::Annotate(_, _) => todo!(),
            Expression::Base(_, exprs) => exprs.iter().try_for_each(map),
            Expression::Record(fields) => fields.iter().map(|(_, expr)| expr).try_for_each(map),
            Expression::Variant(alts) => alts
                .iter()
                .flat_map(|(_, exprs)| exprs.iter())
                .try_for_each(map),
            Expression::Tuple(exprs) => exprs.iter().try_for_each(map),
            Expression::Poly_variant((_, constrs)) => {
                constrs.iter().try_for_each(|constr| match constr {
                    PolyConstr::Constr((_, opt_expr)) => {
                        opt_expr.iter().map(Box::as_ref).try_for_each(map)
                    }
                    PolyConstr::Inherit((_, expr)) => map(expr),
                })
            }
            Expression::Var(_) => Ok(()),
            Expression::Rec_app(_, exprs) => exprs.iter().try_for_each(map),
            Expression::Top_app(Group { gid, members, .. }, _, args) => {
                if let Some(name) = xref.for_gid(*gid).and_then(|(_, name)| name) {
                    let mut file = PathBuf::from(dir).join(name);
                    file.set_extension("shape");
                    expr.sexp_of().write_hum(&mut File::create(&file)?)?;
                }
                members
                    .iter()
                    .map(|(_, (_, expr))| expr)
                    .try_for_each(map)?;
                args.iter().try_for_each(map)
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, ArgEnum, Debug)]
enum ExprKind {
    Record,
    Variant,
    Tuple,
    Base,
}

impl ExprKind {
    fn matches(&self, expr: &Expression) -> bool {
        matches!(
            (self, expr),
            (Self::Record, Expression::Record(..))
                | (Self::Variant, Expression::Variant(..))
                | (Self::Tuple, Expression::Tuple(..))
                | (Self::Base, Expression::Base(..))
        )
    }
}

// fn format_tokens(ts: TokenStream) -> String {
//     RustFmt::default().format_tokens(ts.into()).unwrap()
// }

fn main() -> Result<()> {
    let cli = Cli::parse();
    let file = cli.file;
    let mut r =
        BufReader::new(File::open(&file).map_err(|err| format_err!("cannot open {file}: {err}"))?);
    let shapes = read(
        &mut r, false, // !cli.no_eval
    )?;
    match cli.command {
        Commands::Filter { enable, depth } => {
            struct Filter<'a> {
                matches: bool,
                curr_depth: usize,
                depth: usize,
                enable: &'a Vec<ExprKind>,
            }
            impl<'a> Visitor<'a> for Filter<'a> {
                fn apply(&mut self, expr: &'a Expression) {
                    match self.curr_depth.cmp(&self.depth) {
                        Ordering::Less => {
                            self.curr_depth += 1;
                            expr.visit(self)
                        }
                        Ordering::Equal => {
                            self.matches = self.enable.iter().any(|f| f.matches(expr))
                        }
                        Ordering::Greater => {}
                    }
                }
            }

            for Type { shape, source, .. } in shapes {
                let mut filter = Filter {
                    matches: false,
                    curr_depth: 0,
                    depth: depth.unwrap_or(1),
                    enable: &enable,
                };
                shape.visit(&mut filter);
                if filter.matches {
                    print!("{source}");
                }
            }
            Ok(())
        }
        Commands::Doc { _type, all } => doc(shapes, _type, all),
        Commands::Gen(gen) => gen.run(shapes),
        Commands::Dump(dump) => dump.run(shapes),
    }

    //    let mut gen = Generator::new(&types)?;

    //    let ts = gen.generate("Transaction_snark.Pending_coinbase_stack_state.Stable.V1.t");
    //    println!("{}", format_tokens(ts));
    //
}

fn read(read: &mut impl BufRead, eval: bool) -> Result<Vec<Type>> {
    let mut mina_types = Vec::new();
    let mut buf = String::new();
    while read.read_line(&mut buf)? != 0 {
        let source = std::mem::take(&mut buf);
        let ty = Type::from_mina_shape(source, eval)?;
        mina_types.push(ty);
    }
    Ok(mina_types)
}

fn doc(shapes: Vec<Type>, _types: Vec<String>, all: bool) -> Result<()> {
    if _types.is_empty() != all {
        bail!("should be either --type or --all");
    }

    let xref = XRef::new(&shapes)?;
    let git_base =
        "https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/";
    let mut stdout = std::io::stdout();

    if all {
        let mut doc = Doc::new(&xref, git_base.to_string(), &mut stdout);
        doc.generate_all()?;
    } else {
        for _type in &_types {
            let mut doc = Doc::new(&xref, git_base.to_string(), &mut stdout);
            doc.generate(_type)?;
        }
    }

    Ok(())
}

impl Gen {
    fn run(self, shapes: Vec<Type>) -> Result<()> {
        if self.types.is_empty() != self.all {
            bail!("should be either --all or [TYPES]");
        }

        let xref = XRef::new(&shapes)?;
        let git_base =
            "https://github.com/MinaProtocol/mina/blob/b14f0da9ebae87acd8764388ab4681ca10f07c89/";

        let config = if let Some(config) = self.config {
            let mut buf = Vec::new();
            File::open(config)?.read_to_end(&mut buf)?;
            toml::from_slice(&buf)?
        } else {
            bin_prot_rs::gen::ConfigBuilder::default()
                .generate_comments(true)
                .blank_lines(true)
                .git_prefix(git_base)
                .build()?
        };
        let mut gen = bin_prot_rs::gen::Generator::new(&xref, config);
        let ts = if self.all {
            gen.generate_types(xref.names())
        } else {
            gen.generate_types(&self.types)
        };
        let config = rust_format::Config::new_str()
            .post_proc(rust_format::PostProcess::ReplaceMarkersAndDocBlocks);

        match RustFmt::from_config(config).format_tokens(ts.into()) {
            Ok(res) => {
                if let Some(out) = self.out {
                    File::create(out)?.write_all(res.as_bytes())?;
                } else {
                    std::io::stdout().write_all(res.as_bytes())?;
                }
            }
            Err(rust_format::Error::BadSourceCode(err)) => {
                eprintln!("Error formatting tokens\n{err}")
            }
            Err(err) => {
                eprintln!("Error formatting tokens: {err}")
            }
        }
        Ok(())
    }
}

struct Type {
    name: String,
    shape: Expression,
    source: String,
}

impl NamedShape for Type {
    fn name(&self) -> &str {
        &self.name
    }

    fn shape(&self) -> &Expression {
        &self.shape
    }
}

impl Type {
    fn from_mina_shape(source: String, eval: bool) -> Result<Self, anyhow::Error> {
        let mut parts = source.splitn(2, ", ");
        let ty = parts
            .next()
            .ok_or_else(|| format_err!("missing type description"))?;
        let (_, name) = ty
            .split_once(':')
            .ok_or_else(|| format_err!("invalid descriptor format"))?;
        let shape = parts
            .next()
            .ok_or_else(|| format_err!("missing shape for {name}"))?;
        let shape = shape
            .parse()
            .map_err(|e| format_err!("error while reading {name}: {e}"))?;
        Ok(Self {
            name: name.to_string(),
            shape: if eval {
                bin_prot_rs::eval::eval(&shape)?
            } else {
                shape
            },
            source,
        })
    }
}
