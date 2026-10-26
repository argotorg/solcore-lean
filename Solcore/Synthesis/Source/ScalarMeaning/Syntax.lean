/-! Abstract syntax of the Rust-dialect source fragment printed by the scalar
source renderers and their wrappers: the closed (`run()`), runtime-input and
named-helper (`run(uint256)`) contracts. This is the source side of the
emitter proofs; it does not mention Core. Indentation and spacing belong to
the printer, not to this syntax. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.ScalarMeaning

/-- Type annotations admitted on `let` declarations and helper signatures:
`word` and `bool`. -/
inductive LocalType where
  | word
  | bool
  deriving Repr, BEq, DecidableEq

/-- Prefix operators `!` and `~`. -/
inductive UnaryOp where
  | not
  | bitNot
  deriving Repr, BEq, DecidableEq

/-- Infix operators `+`, `-`, `*`, `&`, `|`, `^`, `==` and `>`. -/
inductive BinaryOp where
  | add
  | sub
  | mul
  | bitAnd
  | bitOr
  | bitXor
  | eq
  | gt
  deriving Repr, BEq, DecidableEq

/-- Expressions. Operator applications are always parenthesized, so the
fragment needs no precedence rules. `typedefRep` is the call
`Typedef.rep(e)`, `uint256` is the constructor call `uint256(e)` and
`call1` to `call3` call a named function with one to three arguments. -/
inductive Expr where
  | name (identifier : String)
  | number (value : Nat)
  | bool (value : Bool)
  | unary (op : UnaryOp) (operand : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | typedefRep (operand : Expr)
  | uint256 (operand : Expr)
  | call1 (callee : String) (first : Expr)
  | call2 (callee : String) (first second : Expr)
  | call3 (callee : String) (first second third : Expr)
  deriving Repr, BEq, DecidableEq

/-- Statements: `let x: T = e;`, `x = e;` and `if (c) { .. } else { .. }`. -/
inductive Stmt where
  | letDecl (identifier : String) (type : LocalType) (initializer : Expr)
  | assign (identifier : String) (value : Expr)
  | ifElse (condition : Expr) (thenBlock elseBlock : List Stmt)
  deriving Repr

/-- A free function before the contract. Its body ends with `return result;`. -/
structure FunctionDecl where
  name : String
  parameters : List (String × LocalType)
  resultType : LocalType
  body : List Stmt
  result : Expr
  deriving Repr

/-- A public method whose parameters and declared result all have type
`uint256`; `result` is the expression of its final `return`. -/
structure Method where
  name : String
  parameters : List String
  body : List Stmt
  result : Expr
  deriving Repr

/-- A source file importing `std` and `std.dispatch`, optionally importing
`opcode as alias` pairs from `std.opcodes`, declaring free functions, and
declaring one contract with one method. -/
structure SourceFile where
  opcodeAliases : List (String × String)
  functions : List FunctionDecl
  contract : String
  method : Method
  deriving Repr

def LocalType.spelling : LocalType → String
  | .word => "word"
  | .bool => "bool"

def UnaryOp.spelling : UnaryOp → String
  | .not => "!"
  | .bitNot => "~"

def BinaryOp.spelling : BinaryOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .bitAnd => "&"
  | .bitOr => "|"
  | .bitXor => "^"
  | .eq => "=="
  | .gt => ">"

/-- Every identifier occurring in an expression, including callees, in
preorder. -/
def Expr.identifiers : Expr → List String
  | .name identifier => [identifier]
  | .number _ | .bool _ => []
  | .unary _ operand | .typedefRep operand | .uint256 operand => operand.identifiers
  | .binary _ left right => left.identifiers ++ right.identifiers
  | .call1 callee first => callee :: first.identifiers
  | .call2 callee first second => callee :: (first.identifiers ++ second.identifiers)
  | .call3 callee first second third =>
      callee :: (first.identifiers ++ second.identifiers ++ third.identifiers)

mutual

/-- Every declared, assigned or referenced identifier, in preorder. -/
def Stmt.identifiers : Stmt → List String
  | .letDecl identifier _ initializer => identifier :: initializer.identifiers
  | .assign identifier value => identifier :: value.identifiers
  | .ifElse condition thenBlock elseBlock =>
      condition.identifiers ++ Stmt.listIdentifiers thenBlock ++
        Stmt.listIdentifiers elseBlock

def Stmt.listIdentifiers : List Stmt → List String
  | [] => []
  | statement :: rest => statement.identifiers ++ Stmt.listIdentifiers rest

end

theorem Stmt.listIdentifiers_append (first second : List Stmt) :
    Stmt.listIdentifiers (first ++ second) =
      Stmt.listIdentifiers first ++ Stmt.listIdentifiers second := by
  induction first with
  | nil => simp [Stmt.listIdentifiers]
  | cons statement rest ih =>
      simp [Stmt.listIdentifiers, ih, List.append_assoc]

/-- The identifiers of a free function: its name, parameters, body and
result. -/
def FunctionDecl.identifiers (function : FunctionDecl) : List String :=
  function.name :: function.parameters.map Prod.fst ++ Stmt.listIdentifiers function.body ++
    function.result.identifiers

end Solcore.Synthesis.Source.ScalarMeaning
