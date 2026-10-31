//! Export the pinned parser's mutation sites of one source file: literals, binary, unary and compound-assignment
//! operators and conditions, and inline Yul literals, builtin calls and conditions, each with its absolute byte span
//! and the source text there. A site whose text is not the token its node names is reported as unsafe. The parser
//! lowers `x += e` to a plain assignment of a binary operator whose token span covers `+=`, so such a token is a
//! compound-assignment site.
use hir::{
    arena::Arena,
    ast::{
        function::{BinOp, Expr, ExprKind, FuncBody, LitKind, PatKind, StmtKind, UnOp, YulExpr, YulExprKind,
                   YulLitKind, YulStmt, YulStmtKind},
        item::{ContractItem, FunctionDef, Item},
    },
    input::SourceFile,
    span::{Span, Spanned},
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

fn binary(op: BinOp) -> Option<(&'static str, &'static str)> {
    Some(match op {
        BinOp::Add => ("add", "+"),
        BinOp::Sub => ("sub", "-"),
        BinOp::Mul => ("mul", "*"),
        BinOp::Div => ("div", "/"),
        BinOp::Mod => ("mod", "%"),
        BinOp::BitAnd => ("bit-and", "&"),
        BinOp::BitXor => ("bit-xor", "^"),
        BinOp::BitOr => ("bit-or", "|"),
        BinOp::Eq => ("eq", "=="),
        BinOp::NotEq => ("not-eq", "!="),
        BinOp::Lt => ("lt", "<"),
        BinOp::Gt => ("gt", ">"),
        BinOp::LtEq => ("lt-eq", "<="),
        BinOp::GtEq => ("gt-eq", ">="),
        BinOp::And => ("and", "&&"),
        BinOp::Or => ("or", "||"),
        BinOp::Error => return None,
    })
}

struct Sites<'a> {
    db: &'a Db,
    text: &'a str,
    owner: String,
    sites: Vec<Value>,
    unsafe_sites: Vec<Value>,
}

impl<'a> Sites<'a> {
    fn range(&self, span: Span<'_>) -> (usize, usize) {
        let absolute = span.resolve_to_absolute(self.db);
        (absolute.start.as_u32() as usize, absolute.end.as_u32() as usize)
    }

    fn slice(&self, (start, end): (usize, usize)) -> Option<&'a str> {
        self.text.get(start..end)
    }

    /// Records a site when the source text at its span is `expected`, else an unsafe site.
    fn site(&mut self, mut value: Value, range: (usize, usize), expected: &[&str]) {
        let found = self.slice(range).map(str::to_owned);
        value["span"] = json!([range.0, range.1]);
        value["owner"] = json!(self.owner);
        value["text"] = json!(found);
        if found.as_deref().is_some_and(|text| expected.contains(&text)) {
            self.sites.push(value);
        } else {
            value["expected"] = json!(expected);
            self.unsafe_sites.push(value);
        }
    }

    fn literal(&mut self, kind: &LitKind, range: (usize, usize), pattern: bool) {
        let (name, text) = match kind {
            LitKind::Number(text) => ("number", text.clone()),
            LitKind::Hex(text) => ("hex", text.clone()),
            LitKind::String(text) => ("string", text.clone()),
            LitKind::Error => return,
        };
        let quoted = format!("\"{text}\"");
        let expected = [text.as_str(), quoted.as_str()];
        self.site(json!({"kind":"literal", "literal":name, "value":text, "pattern":pattern}), range, &expected);
    }

    fn condition(&mut self, context: &str, range: (usize, usize)) {
        let text = self.slice(range).unwrap_or_default().to_owned();
        self.site(json!({"kind":"condition", "context":context}), range, &[text.as_str()]);
    }

    fn expressions(&mut self, exprs: &Arena<Expr<'_>>) {
        for (_, expr) in exprs.iter() {
            let range = self.range(expr.span);
            match &expr.kind {
                ExprKind::Lit(kind) => self.literal(kind, range, false),
                ExprKind::BinOp { op, .. } => {
                    if let Some((name, token)) = binary(*op.atom()) {
                        let token_range = self.range(op.span(self.db));
                        let compound = format!("{token}=");
                        let kind = if self.slice(token_range) == Some(compound.as_str()) { "assign" } else { "binary" };
                        let expected = if kind == "assign" { compound.as_str() } else { token };
                        self.site(json!({"kind":kind, "op":name, "expr":[range.0, range.1]}), token_range, &[expected]);
                    }
                }
                ExprKind::UnaryOp { op, .. } => {
                    let name = match op.atom() {
                        UnOp::Not => ("not", "!"),
                        UnOp::BitNot => ("bit-not", "~"),
                        UnOp::Error => continue,
                    };
                    let token_range = self.range(op.span(self.db));
                    self.site(json!({"kind":"unary", "op":name.0, "expr":[range.0, range.1]}), token_range, &[name.1]);
                }
                ExprKind::If { cond, .. } => {
                    let cond_range = self.range(exprs[*cond].span);
                    self.condition("if-expr", cond_range);
                }
                ExprKind::Lambda { body, .. } => self.body(*body),
                _ => {}
            }
        }
    }

    fn body(&mut self, body: FuncBody<'_>) {
        let db = self.db;
        let exprs = body.exprs(db);
        self.expressions(exprs);
        for (_, stmt) in body.stmts(db).iter() {
            match &stmt.kind {
                StmtKind::If { cond, .. } => {
                    let range = self.range(exprs[*cond].span);
                    self.condition("if", range);
                }
                StmtKind::For { cond, .. } => {
                    let range = self.range(exprs[*cond].span);
                    self.condition("for", range);
                }
                StmtKind::Assembly { body } => self.yul(body),
                _ => {}
            }
        }
        for (_, pat) in body.pats(db).iter() {
            if let PatKind::Lit(kind) = &pat.kind {
                let range = self.range(pat.span);
                self.literal(kind, range, true);
            }
        }
    }

    fn yul_expr(&mut self, expr: &YulExpr<'_>) {
        let range = self.range(expr.span);
        match &expr.kind {
            YulExprKind::Lit(kind) => {
                let (name, text) = match kind {
                    YulLitKind::Number(text) => ("number", text.clone()),
                    YulLitKind::Hex(text) => ("hex", text.clone()),
                    YulLitKind::String(text) => ("string", text.clone()),
                    YulLitKind::Bool(value) => ("bool", value.to_string()),
                    YulLitKind::Error => return,
                };
                let quoted = format!("\"{text}\"");
                let expected = [text.as_str(), quoted.as_str()];
                self.site(json!({"kind":"yul-literal", "literal":name, "value":text}), range, &expected);
            }
            YulExprKind::Call { name, args } => {
                let name_range = self.range(name.span(self.db));
                let callee = name.atom().text(self.db).to_owned();
                self.site(json!({"kind":"yul-call", "name":callee, "expr":[range.0, range.1]}), name_range,
                          &[callee.as_str()]);
                for arg in args {
                    self.yul_expr(arg);
                }
            }
            YulExprKind::Ident(_) | YulExprKind::Error => {}
        }
    }

    fn yul(&mut self, stmts: &[YulStmt<'_>]) {
        for stmt in stmts {
            match &stmt.kind {
                YulStmtKind::Block(body) => self.yul(body),
                YulStmtKind::Let { init, .. } => {
                    if let Some(init) = init {
                        self.yul_expr(init);
                    }
                }
                YulStmtKind::Assign { value, .. } | YulStmtKind::Expr(value) => self.yul_expr(value),
                YulStmtKind::If { cond, body } => {
                    let range = self.range(cond.span);
                    let text = self.slice(range).unwrap_or_default().to_owned();
                    self.site(json!({"kind":"yul-condition", "context":"if"}), range, &[text.as_str()]);
                    self.yul_expr(cond);
                    self.yul(body);
                }
                YulStmtKind::For { init, cond, post, body } => {
                    self.yul(init);
                    let range = self.range(cond.span);
                    let text = self.slice(range).unwrap_or_default().to_owned();
                    self.site(json!({"kind":"yul-condition", "context":"for"}), range, &[text.as_str()]);
                    self.yul_expr(cond);
                    self.yul(post);
                    self.yul(body);
                }
                YulStmtKind::Switch { expr, cases, default } => {
                    self.yul_expr(expr);
                    for case in cases {
                        self.yul(&case.body);
                    }
                    if let Some(default) = default {
                        self.yul(default);
                    }
                }
                YulStmtKind::FunctionDef { body, .. } => self.yul(body),
                YulStmtKind::Leave | YulStmtKind::Break | YulStmtKind::Continue | YulStmtKind::Error => {}
            }
        }
    }

    fn function(&mut self, owner: String, function: FunctionDef<'_>) {
        self.owner = owner;
        if let Some(body) = function.body(self.db) {
            self.body(body);
        }
    }
}

fn extract(path: &Path) -> Result<Value, String> {
    let source = fs::read_to_string(path).map_err(|error| error.to_string())?;
    let db = Db::default();
    let file = SourceFile::new(
        &db,
        url::Url::from_file_path(path).map_err(|_| "invalid source path")?,
        Some(source.clone()),
    );
    let hir = parser::parse_file_to_hir(&db, file);
    if !hir.diagnostics(&db).is_empty() {
        return Err(format!("source parser returned {} diagnostics", hir.diagnostics(&db).len()));
    }
    let mut sites = Sites { db: &db, text: &source, owner: String::new(), sites: Vec::new(), unsafe_sites: Vec::new() };
    for item in hir.module(&db).items(&db) {
        match *item {
            Item::FunctionDef(function) => {
                let name = function.sig(&db).name.atom().text(&db).to_owned();
                sites.function(name, function);
            }
            Item::ContractDef(contract) => {
                let contract_name = contract.name_elem(&db).atom().text(&db).to_owned();
                for field in contract.fields(&db) {
                    if let Some(init) = field.init() {
                        sites.owner = format!("{contract_name}.{}", field.name().atom().text(&db));
                        sites.expressions(&init.exprs);
                    }
                }
                for item in contract.items(&db) {
                    match *item {
                        ContractItem::FunctionDef(function) => {
                            let name = function.sig(&db).name.atom().text(&db).to_owned();
                            sites.function(format!("{contract_name}.{name}"), function);
                        }
                        ContractItem::Error { .. } => return Err("contract item parser recovery".into()),
                        ContractItem::TypeAlias(_) | ContractItem::AdtDef(_) => {}
                    }
                }
            }
            Item::InstanceDef(instance) => {
                let start = sites.range(instance.span(&db)).0;
                for method in instance.methods(&db) {
                    let name = method.sig(&db).name.atom().text(&db).to_owned();
                    sites.function(format!("instance@{start}.{name}"), *method);
                }
            }
            Item::Error { .. } => return Err("item parser recovery".into()),
            Item::Import(_) | Item::AdtDef(_) | Item::TypeAlias(_) | Item::ClassDef(_) | Item::Export(_)
            | Item::Pragma(_) => {}
        }
    }
    let mut found = sites.sites;
    found.sort_by_key(|site| (site["span"][0].as_u64(), site["span"][1].as_u64()));
    Ok(json!({"schema":"solcore-rs.sites.v1", "upstreamCommit":COMMIT, "source":path.to_string_lossy(),
        "bytes":source.len(), "sites":found, "unsafe":sites.unsafe_sites}))
}

fn main() {
    let result = (|| {
        let path = env::args().nth(1).ok_or("usage: solcore-site-export SOURCE.sol")?;
        extract(&Path::new(&path).canonicalize().map_err(|error| error.to_string())?)
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
