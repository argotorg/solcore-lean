//! Lossless typed Hull transport for solcore-lean's pinned import boundary.
//! This module is installed only into an isolated upstream checkout. The
//! ordinary checked-Hull pipeline runs before this serialization function.

use hir::{
    ast::{
        Ident,
        function::{YulExpr, YulExprKind, YulLitKind, YulStmt, YulStmtKind},
    },
    span::{Span, Spanned, SpannedElem},
};
use hull::{
    Con, Expr, ExprKind, Function, Object, Pat, PatKind, Program, Stmt, StmtKind, Ty, TyKind,
};
use serde_json::{Value, json};

const UPSTREAM_COMMIT: &str = "2a745e12974c373c3799fec81b48a53c7dce2ab4";

fn span<'db>(db: &'db dyn hir::Db, value: Span<'db>) -> Value {
    let absolute = value.resolve_to_absolute(db);
    json!({"file": absolute.file.url(db).as_str(),
        "start": absolute.start.as_u32(), "end": absolute.end.as_u32()})
}

fn located<'db>(db: &'db dyn hir::Db, source: Span<'db>, mut value: Value) -> Value {
    value
        .as_object_mut()
        .expect("transport object")
        .insert("span".into(), span(db, source));
    value
}

fn ty<'db>(db: &'db dyn hir::Db, value: &Ty<'db>) -> Value {
    let result = match &value.kind {
        TyKind::Word => json!({"tag": "word"}),
        TyKind::Bool => json!({"tag": "bool"}),
        TyKind::Unit => json!({"tag": "unit"}),
        TyKind::Product(left, right) => {
            json!({"tag":"product", "left":ty(db,left), "right":ty(db,right)})
        }
        TyKind::Sum(left, right) => json!({"tag":"sum", "left":ty(db,left), "right":ty(db,right)}),
        TyKind::Named { name, inner } => {
            json!({"tag":"named", "name":name.as_str(), "inner":ty(db,inner)})
        }
        TyKind::NamedRef { name } => json!({"tag":"namedRef", "name":name.as_str()}),
        TyKind::Function { params, ret } => {
            json!({"tag":"function", "params":params.iter().map(|p| ty(db,p)).collect::<Vec<_>>(), "ret":ty(db,ret)})
        }
    };
    located(db, value.span, result)
}

fn expr<'db>(db: &'db dyn hir::Db, value: &Expr<'db>) -> Value {
    let mut result = match &value.kind {
        ExprKind::Word(value) => json!({"tag":"word", "value":value}),
        ExprKind::Bool(value) => json!({"tag":"bool", "value":value}),
        ExprKind::Unit => json!({"tag":"unit"}),
        ExprKind::Var(name) => json!({"tag":"var", "name":name.as_str()}),
        ExprKind::Pair(left, right) => {
            json!({"tag":"pair", "left":expr(db,left), "right":expr(db,right)})
        }
        ExprKind::Fst(value) => json!({"tag":"fst", "value":expr(db,value)}),
        ExprKind::Snd(value) => json!({"tag":"snd", "value":expr(db,value)}),
        ExprKind::Inl { target, value } => {
            json!({"tag":"inl", "target":ty(db,target), "value":expr(db,value)})
        }
        ExprKind::Inr { target, value } => {
            json!({"tag":"inr", "target":ty(db,target), "value":expr(db,value)})
        }
        ExprKind::InK {
            index,
            target,
            value,
        } => json!({"tag":"inK", "index":index, "target":ty(db,target), "value":expr(db,value)}),
        ExprKind::Call { callee, args } => {
            json!({"tag":"call", "callee":callee.as_str(), "args":args.iter().map(|a| expr(db,a)).collect::<Vec<_>>()})
        }
        ExprKind::If {
            target,
            cond,
            then_expr,
            else_expr,
        } => {
            json!({"tag":"if", "target":ty(db,target), "cond":expr(db,cond), "thenExpr":expr(db,then_expr), "elseExpr":expr(db,else_expr)})
        }
    };
    result
        .as_object_mut()
        .expect("expression object")
        .insert("ty".into(), ty(db, &value.ty));
    located(db, value.span, result)
}

fn con(value: Con) -> Value {
    match value {
        Con::Inl => json!({"tag":"inl"}),
        Con::Inr => json!({"tag":"inr"}),
        Con::InK(index) => json!({"tag":"inK", "index":index}),
    }
}

fn pat<'db>(db: &'db dyn hir::Db, value: &Pat<'db>) -> Value {
    let result = match &value.kind {
        PatKind::Var(name) => json!({"tag":"var", "name":name.as_str()}),
        PatKind::Con(value) => json!({"tag":"con", "value":con(*value)}),
        PatKind::Wildcard => json!({"tag":"wildcard"}),
        PatKind::IntLit(value) => json!({"tag":"intLit", "value":value}),
    };
    located(db, value.span, result)
}

fn stmts<'db>(db: &'db dyn hir::Db, values: &[Stmt<'db>]) -> Vec<Value> {
    values.iter().map(|value| stmt(db, value)).collect()
}

fn stmt<'db>(db: &'db dyn hir::Db, value: &Stmt<'db>) -> Value {
    let result = match &value.kind {
        StmtKind::Let {
            name,
            ty: annotation,
        } => json!({"tag":"let", "name":name.as_str(), "ty":ty(db,annotation)}),
        StmtKind::Assign { lhs, rhs } => {
            json!({"tag":"assign", "lhs":expr(db,lhs), "rhs":expr(db,rhs)})
        }
        StmtKind::Expr(value) => json!({"tag":"expr", "value":expr(db,value)}),
        StmtKind::Return(value) => json!({"tag":"return", "value":expr(db,value)}),
        StmtKind::Block(body) => json!({"tag":"block", "body":stmts(db,body)}),
        StmtKind::For {
            init,
            cond,
            post,
            body,
        } => {
            json!({"tag":"for", "init":stmts(db,init), "cond":expr(db,cond), "post":stmts(db,post), "body":stmts(db,body)})
        }
        StmtKind::Break => json!({"tag":"break"}),
        StmtKind::Continue => json!({"tag":"continue"}),
        StmtKind::Match {
            target,
            scrutinee,
            alts,
        } => {
            json!({"tag":"match", "target":ty(db,target), "scrutinee":expr(db,scrutinee), "alts":alts.iter().map(|alt| located(db,alt.span,json!({"pat":pat(db,&alt.pat),"binder":alt.binder.as_str(),"body":stmts(db,&alt.body)}))).collect::<Vec<_>>()})
        }
        StmtKind::Assembly(body) => json!({"tag":"assembly", "body":yul_stmts(db,body)}),
        StmtKind::Revert(message) => json!({"tag":"revert", "message":message}),
        StmtKind::Comment(text) => json!({"tag":"comment", "text":text}),
    };
    located(db, value.span, result)
}

fn function<'db>(db: &'db dyn hir::Db, value: &Function<'db>) -> Value {
    located(
        db,
        value.span,
        json!({"name":value.name.as_str(),
        "args":value.args.iter().map(|arg| located(db,arg.span,json!({"name":arg.name.as_str(),"ty":ty(db,&arg.ty)}))).collect::<Vec<_>>(),
        "ret":ty(db,&value.ret),"body":stmts(db,&value.body)}),
    )
}

fn object<'db>(db: &'db dyn hir::Db, value: &Object<'db>) -> Value {
    located(
        db,
        value.span,
        json!({"name":value.name.as_str(),
        "code":located(db,value.code.span,json!({"stmts":stmts(db,&value.code.stmts),"functions":value.code.functions.iter().map(|f| function(db,f)).collect::<Vec<_>>()})),
        "inners":value.inners.iter().map(|o| object(db,o)).collect::<Vec<_>>()}),
    )
}

fn yul_name<'db>(db: &'db dyn hir::Db, value: &SpannedElem<'db, Ident<'db>>) -> Value {
    located(db, value.span(db), json!({"name":(*value.atom()).text(db)}))
}

fn yul_names<'db>(db: &'db dyn hir::Db, values: &[SpannedElem<'db, Ident<'db>>]) -> Vec<Value> {
    values.iter().map(|name| yul_name(db, name)).collect()
}

fn yul_lit(value: &YulLitKind) -> Value {
    match value {
        YulLitKind::Number(value) => json!({"tag":"number","value":value}),
        YulLitKind::Hex(value) => json!({"tag":"hex","value":value}),
        YulLitKind::String(value) => json!({"tag":"string","value":value}),
        YulLitKind::Bool(value) => json!({"tag":"bool","value":value}),
        YulLitKind::Error => panic!("checked Hull contained a recovered Yul literal"),
    }
}

fn yul_expr<'db>(db: &'db dyn hir::Db, value: &YulExpr<'db>) -> Value {
    let result = match &value.kind {
        YulExprKind::Lit(value) => json!({"tag":"literal","value":yul_lit(value)}),
        YulExprKind::Ident(name) => json!({"tag":"ident","name":yul_name(db,name)}),
        YulExprKind::Call { name, args } => {
            json!({"tag":"call","name":yul_name(db,name),"args":args.iter().map(|a| yul_expr(db,a)).collect::<Vec<_>>()})
        }
        YulExprKind::Error => panic!("checked Hull contained a recovered Yul expression"),
    };
    located(db, value.span, result)
}

fn yul_stmts<'db>(db: &'db dyn hir::Db, values: &[YulStmt<'db>]) -> Vec<Value> {
    values.iter().map(|value| yul_stmt(db, value)).collect()
}

fn yul_stmt<'db>(db: &'db dyn hir::Db, value: &YulStmt<'db>) -> Value {
    let result = match &value.kind {
        YulStmtKind::Block(body) => json!({"tag":"block","body":yul_stmts(db,body)}),
        YulStmtKind::Let { names, init } => {
            json!({"tag":"let","names":yul_names(db,names),"init":init.as_ref().map(|i| yul_expr(db,i))})
        }
        YulStmtKind::Assign { names, value } => {
            json!({"tag":"assign","names":yul_names(db,names),"value":yul_expr(db,value)})
        }
        YulStmtKind::Expr(value) => json!({"tag":"expr","value":yul_expr(db,value)}),
        YulStmtKind::If { cond, body } => {
            json!({"tag":"if","cond":yul_expr(db,cond),"body":yul_stmts(db,body)})
        }
        YulStmtKind::For {
            init,
            cond,
            post,
            body,
        } => {
            json!({"tag":"for","init":yul_stmts(db,init),"cond":yul_expr(db,cond),"post":yul_stmts(db,post),"body":yul_stmts(db,body)})
        }
        YulStmtKind::Switch {
            expr: expression,
            cases,
            default,
        } => {
            json!({"tag":"switch","value":yul_expr(db,expression),"cases":cases.iter().map(|case| located(db,case.span,json!({"lit":yul_lit(&case.lit),"body":yul_stmts(db,&case.body)}))).collect::<Vec<_>>(),"defaultBody":default.as_ref().map(|body| yul_stmts(db,body))})
        }
        YulStmtKind::FunctionDef {
            name,
            params,
            rets,
            body,
        } => {
            json!({"tag":"function","name":yul_name(db,name),"params":yul_names(db,params),"rets":yul_names(db,rets),"body":yul_stmts(db,body)})
        }
        YulStmtKind::Leave => json!({"tag":"leave"}),
        YulStmtKind::Break => json!({"tag":"break"}),
        YulStmtKind::Continue => json!({"tag":"continue"}),
        YulStmtKind::Error => panic!("checked Hull contained a recovered Yul statement"),
    };
    located(db, value.span, result)
}

pub(crate) fn export<'db>(db: &'db dyn hir::Db, program: &Program<'db>) -> String {
    json!({"schema":"solcore-rs.hull.v1", "upstreamCommit":UPSTREAM_COMMIT,
    "program":located(db,program.span,json!({
        "entryPoints":program.entry_points.iter().map(|n| n.as_str()).collect::<Vec<_>>(),
        "functions":program.functions.iter().map(|f| function(db,f)).collect::<Vec<_>>(),
        "objects":program.objects.iter().map(|o| object(db,o)).collect::<Vec<_>>()
    }))})
    .to_string()
}
