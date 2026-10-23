//! Minimized upstream Hull/Yul name-resolution probe for questions.md.
//! Copy into crates/yul/examples/lean_hull_call_probe.rs in the pinned checkout,
//! then run cargo run -p solcore-yul --example lean_hull_call_probe --offline.
use hir::{
    anchor::DefLocationTable,
    ast::{
        function::{YulExpr, YulExprKind, YulStmt, YulStmtKind},
        Ident,
    },
    diag::Offset,
    input::SourceFile,
    span::{AnchorId, Span, SpannedElem},
};
use hull::{Expr, Function, Program, Stmt, StmtKind, Ty};
use parser::parse_file_to_hir;

#[salsa::db]
#[derive(Default, Clone)]
struct Db {
    storage: salsa::Storage<Self>,
}
#[salsa::db]
impl salsa::Database for Db {}
#[salsa::db]
impl hir::Db for Db {
    fn def_location_table<'db>(&'db self, file: SourceFile) -> &'db DefLocationTable<'db> {
        parse_file_to_hir(self, file).def_locations(self)
    }
}
#[salsa::db]
impl parser::Db for Db {}

fn main() {
    let db = Db::default();
    let file = SourceFile::new(
        &db,
        "memory:///hull_call_probe.sol".parse().unwrap(),
        Some(String::new()),
    );
    let span = Span::new(AnchorId::root(&db, file), Offset::new(0), Offset::new(0));
    let ident = |name: &str| SpannedElem::new(Ident::new(&db, name.to_owned()), span);
    for callee in ["helper", "usr$helper"] {
        let program = Program {
            span,
            entry_points: vec!["main".into()],
            objects: vec![],
            functions: vec![
                Function {
                    span,
                    name: "helper".into(),
                    args: vec![],
                    ret: Ty::word(span),
                    body: vec![Stmt {
                        span,
                        kind: StmtKind::Return(Expr::word(span, "42")),
                    }],
                },
                Function {
                    span,
                    name: "main".into(),
                    args: vec![],
                    ret: Ty::word(span),
                    body: vec![
                        Stmt {
                            span,
                            kind: StmtKind::Let {
                                name: "result".into(),
                                ty: Ty::word(span),
                            },
                        },
                        Stmt {
                            span,
                            kind: StmtKind::Assembly(vec![YulStmt {
                                span,
                                kind: YulStmtKind::Assign {
                                    names: vec![ident("result")],
                                    value: YulExpr {
                                        span,
                                        kind: YulExprKind::Call {
                                            name: ident(callee),
                                            args: vec![],
                                        },
                                    },
                                },
                            }]),
                        },
                        Stmt {
                            span,
                            kind: StmtKind::Return(Expr::var(span, "result", Ty::word(span))),
                        },
                    ],
                },
            ],
        };
        let diagnostics = hull::check_program_with_db(&db, &program);
        println!("callee={callee}; checker={diagnostics:?}");
        match solcore_yul::render_hull_program(&db, &program) {
            Ok(yul) => println!("{yul}"),
            Err(error) => println!("emit error: {error}"),
        }
    }
}
