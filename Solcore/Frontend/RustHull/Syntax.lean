/-!
A lossless, typed transport of solcore-rs Hull at the pinned upstream revision.
These nodes are compiler input, not evidence that upstream checking succeeded.
The Core lowering must independently validate their annotations and scopes.
-/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

def schemaName : String := "solcore-rs.hull.v1"
def upstreamCommit : String := "2a745e12974c373c3799fec81b48a53c7dce2ab4"

/-- Resolved file offsets; upstream anchor-relative offsets must be resolved first. -/
structure Span where
  file : String
  start : Nat
  stop : Nat
  deriving Repr, BEq, DecidableEq

inductive Ty where
  | word | bool | unit
  | product (left right : Ty)
  | sum (left right : Ty)
  | named (name : String) (inner : Ty)
  | namedRef (name : String)
  | function (params : List Ty) (ret : Ty)
  /-- Type annotations may carry optional source provenance. -/
  | located (span : Span) (inner : Ty)
  deriving Repr, BEq

mutual
  structure Expr where
    ty : Ty
    kind : ExprKind
    span : Option Span := none
    deriving Repr, BEq
  inductive ExprKind where
    | word (value : String)
    | bool (value : Bool)
    | unit
    | var (name : String)
    | pair (left right : Expr)
    | fst (value : Expr)
    | snd (value : Expr)
    | inl (target : Ty) (value : Expr)
    | inr (target : Ty) (value : Expr)
    | inK (index : Nat) (target : Ty) (value : Expr)
    | call (callee : String) (args : List Expr)
    | ifThen (target : Ty) (cond thenExpr elseExpr : Expr)
    deriving Repr, BEq
end

inductive YulLit where
  | number (text : String)
  | hex (text : String)
  /-- Preserve Rust's literal text, including its quoting convention. -/
  | string (text : String)
  | bool (value : Bool)
  deriving Repr, BEq, DecidableEq

structure YulName where
  name : String
  span : Option Span := none
  deriving Repr, BEq, DecidableEq

mutual
  structure YulExpr where
    kind : YulExprKind
    span : Option Span := none
    deriving Repr, BEq
  inductive YulExprKind where
    | literal (value : YulLit)
    | ident (name : YulName)
    | call (name : YulName) (args : List YulExpr)
    deriving Repr, BEq
end

mutual
  structure YulStmt where
    kind : YulStmtKind
    span : Option Span := none
    deriving Repr, BEq
  inductive YulStmtKind where
    | block (body : List YulStmt)
    | letDecl (names : List YulName) (init : Option YulExpr)
    | assign (names : List YulName) (value : YulExpr)
    | expression (value : YulExpr)
    | ifThen (cond : YulExpr) (body : List YulStmt)
    | forLoop (init : List YulStmt) (cond : YulExpr) (post body : List YulStmt)
    | switch (value : YulExpr) (cases : List YulCase) (defaultBody : Option (List YulStmt))
    | functionDef (name : YulName) (params rets : List YulName) (body : List YulStmt)
    | leave | breakStmt | continueStmt
    deriving Repr, BEq
  structure YulCase where
    lit : YulLit
    body : List YulStmt
    span : Option Span := none
    deriving Repr, BEq
end

inductive Con where
  | inl | inr | inK (index : Nat)
  deriving Repr, BEq, DecidableEq

inductive PatKind where
  | var (name : String)
  | con (value : Con)
  | wildcard
  | intLit (value : String)
  deriving Repr, BEq, DecidableEq

structure Pat where
  kind : PatKind
  span : Option Span := none
  deriving Repr, BEq, DecidableEq

mutual
  structure Stmt where
    kind : StmtKind
    span : Option Span := none
    deriving Repr, BEq
  inductive StmtKind where
    | letDecl (name : String) (ty : Ty)
    | assign (lhs rhs : Expr)
    | expression (value : Expr)
    | returnStmt (value : Expr)
    | block (body : List Stmt)
    | forLoop (init : List Stmt) (cond : Expr) (post body : List Stmt)
    | breakStmt | continueStmt
    | matchStmt (target : Ty) (scrutinee : Expr) (alts : List Alt)
    | assembly (body : List YulStmt)
    | revert (message : String)
    | comment (text : String)
    deriving Repr, BEq
  structure Alt where
    pat : Pat
    binder : String
    body : List Stmt
    span : Option Span := none
    deriving Repr, BEq
end

structure Arg where
  name : String
  ty : Ty
  span : Option Span := none
  deriving Repr, BEq

structure Function where
  name : String
  args : List Arg
  ret : Ty
  body : List Stmt
  span : Option Span := none
  deriving Repr, BEq

structure CodeBlock where
  stmts : List Stmt
  functions : List Function
  span : Option Span := none
  deriving Repr, BEq

/-- Hull stores nested objects; byte data is generated later by its backends. -/
inductive Object where
  | object (name : String) (code : CodeBlock) (inners : List Object) (span : Option Span := none)
  deriving Repr, BEq

structure Program where
  entryPoints : List String
  functions : List Function
  objects : List Object
  span : Option Span := none
  deriving Repr, BEq

structure Envelope where
  program : Program
  deriving Repr, BEq

end Solcore.Frontend.RustHull
