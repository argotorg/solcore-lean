//! Export the pinned parser's declarations: data types, type aliases and functions with their source types.
use hir::{
    ast::{
        function::FuncParam,
        item::{AdtDef, ContractItem, FuncKind, FunctionDef, Item, TypeAlias},
        ty::{TypeRef, TypeRefKind},
    },
    input::SourceFile,
};
use serde_json::{Value, json};
use std::{env, fs, path::Path};

const COMMIT: &str = "2a745e12974c373c3799fec81b48a53c7dce2ab4";

#[salsa::db]
#[derive(Default, Clone)]
struct Db {
    storage: salsa::Storage<Self>,
}
#[salsa::db]
impl salsa::Database for Db {}
#[salsa::db]
impl hir::Db for Db {
    fn def_location_table<'db>(
        &'db self,
        file: SourceFile,
    ) -> &'db hir::anchor::DefLocationTable<'db> {
        parser::parse_file_to_hir(self, file).def_locations(self)
    }
}
#[salsa::db]
impl parser::Db for Db {}

/// A source type as written, before name resolution.
fn ty<'db>(db: &'db dyn hir::Db, ty: TypeRef<'db>) -> Value {
    let all = |items: &[TypeRef<'db>]| items.iter().map(|item| self::ty(db, *item)).collect::<Vec<_>>();
    match ty.kind(db) {
        TypeRefKind::Named {
            qualifier,
            name,
            args,
        } => json!({"named":name.atom().text(db),
            "qualifier":qualifier.as_ref().map(|qualifier| qualifier.atom().text(db)),
            "args":all(args.atom())}),
        TypeRefKind::Tuple { elems } => json!({"tuple":all(elems.atom())}),
        TypeRefKind::Fn { params, ret } => {
            json!({"fn":{"params":all(params.atom()), "ret":self::ty(db, *ret)}})
        }
        TypeRefKind::Comptime { inner, .. } => json!({"comptime":self::ty(db, *inner)}),
        TypeRefKind::Error { .. } => json!({"error":true}),
    }
}

fn data<'db>(db: &'db dyn hir::Db, adt: AdtDef<'db>) -> Value {
    let constructors = adt.ctors(db).iter().map(|ctor| json!({"name":ctor.name.atom().text(db),
        "fields":ty(db, *ctor.fields.atom()), "fieldCount":ctor.field_count,
        "fieldNames":ctor.field_names.as_ref().map(|names| names.iter()
            .map(|name| name.atom().text(db)).collect::<Vec<_>>())}));
    json!({"name":adt.name_elem(db).atom().text(db),
        "params":adt.ty_param_elems(db).iter().map(|param| param.atom().text(db)).collect::<Vec<_>>(),
        "constructors":constructors.collect::<Vec<_>>()})
}

fn alias<'db>(db: &'db dyn hir::Db, alias: TypeAlias<'db>) -> Value {
    json!({"name":alias.name_elem(db).atom().text(db),
        "params":alias.ty_param_elems(db).iter().map(|param| param.atom().text(db)).collect::<Vec<_>>(),
        "type":ty(db, alias.ty(db))})
}

fn function<'db>(db: &'db dyn hir::Db, function: FunctionDef<'db>) -> Value {
    let sig = function.sig(db);
    let params = sig.params.atom().iter().map(|param| match param {
        FuncParam::Typed { comptime, name, ty } => {
            json!({"name":name.atom().text(db), "comptime":comptime.is_some(), "type":self::ty(db, *ty)})
        }
        FuncParam::Untyped { comptime, name } => {
            json!({"name":name.atom().text(db), "comptime":comptime.is_some(), "type":null})
        }
        FuncParam::Error { .. } => json!({"error":true}),
    });
    let kind = match function.kind(db) {
        FuncKind::Function => "function",
        FuncKind::Constructor => "constructor",
        FuncKind::Fallback => "fallback",
    };
    json!({"name":sig.name.atom().text(db), "kind":kind, "public":sig.public.is_some(),
        "payable":sig.payable.is_some(), "params":params.collect::<Vec<_>>(),
        "returns":sig.ret.map(|ret| ty(db, ret))})
}

fn extract(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let db = Db::default();
    let file = SourceFile::new(
        &db,
        url::Url::from_file_path(path).map_err(|_| "invalid source path")?,
        Some(source),
    );
    let hir = parser::parse_file_to_hir(&db, file);
    if !hir.diagnostics(&db).is_empty() {
        return Err(format!(
            "source parser returned {} diagnostics",
            hir.diagnostics(&db).len()
        ));
    }
    let module = hir.module(&db);
    let (mut imports, mut datas, mut aliases, mut functions, mut contracts) =
        (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for item in module.items(&db) {
        match *item {
            Item::Import(import) => imports.push(json!(import.path_elems(&db).iter()
                .map(|part| part.atom().text(&db)).collect::<Vec<_>>())),
            Item::AdtDef(adt) => datas.push(data(&db, adt)),
            Item::TypeAlias(item) => aliases.push(alias(&db, item)),
            Item::FunctionDef(item) => functions.push(function(&db, item)),
            Item::ContractDef(contract) => {
                let (mut local_data, mut local_aliases, mut methods) = (Vec::new(), Vec::new(), Vec::new());
                for item in contract.items(&db) {
                    match *item {
                        ContractItem::FunctionDef(item) => methods.push(function(&db, item)),
                        ContractItem::TypeAlias(item) => local_aliases.push(alias(&db, item)),
                        ContractItem::AdtDef(adt) => local_data.push(data(&db, adt)),
                        ContractItem::Error { .. } => return Err("contract item parser recovery".into()),
                    }
                }
                contracts.push(json!({"name":contract.name_elem(&db).atom().text(&db),
                    "params":contract.ty_param_elems(&db).iter().map(|param| param.atom().text(&db)).collect::<Vec<_>>(),
                    "runtimeMain":contract.has_runtime_main(&db), "data":local_data,
                    "aliases":local_aliases, "functions":methods}));
            }
            Item::Error { .. } => return Err("item parser recovery".into()),
            Item::ClassDef(_) | Item::InstanceDef(_) | Item::Export(_) | Item::Pragma(_) => {}
        }
    }
    Ok(json!({"schema":"solcore-rs.declarations.v1", "upstreamCommit":COMMIT,
        "source":path.to_string_lossy(), "imports":imports, "data":datas, "aliases":aliases,
        "functions":functions, "contracts":contracts}))
}

fn main() {
    let result = (|| {
        let path = env::args()
            .nth(1)
            .ok_or("usage: solcore-declaration-export SOURCE.sol")?;
        extract(
            &Path::new(&path)
                .canonicalize()
                .map_err(|error| error.to_string())?,
        )
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
