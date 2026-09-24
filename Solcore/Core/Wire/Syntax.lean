import Solcore.Core.Syntax

/-! Canonical syntax for the Semantic Core wire boundary. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

structure DataTypeId where
  index : Nat
  deriving Repr, BEq, DecidableEq

namespace DataTypeId

def toCore (id : DataTypeId) : Solcore.Core.DataTypeId :=
  { index := id.index }

def ofCore (id : Solcore.Core.DataTypeId) : DataTypeId :=
  { index := id.index }

@[simp] theorem ofCore_toCore (id : DataTypeId) :
    ofCore id.toCore = id := by
  cases id
  rfl

@[simp] theorem toCore_ofCore (id : Solcore.Core.DataTypeId) :
    toCore (ofCore id) = id := by
  cases id
  rfl

end DataTypeId

structure ConstructorId where
  owner : DataTypeId
  index : Nat
  deriving Repr, BEq, DecidableEq

namespace ConstructorId

def toCore (id : ConstructorId) : Solcore.Core.ConstructorId :=
  { owner := id.owner.toCore, index := id.index }

def ofCore (id : Solcore.Core.ConstructorId) : ConstructorId :=
  { owner := .ofCore id.owner, index := id.index }

@[simp] theorem ofCore_toCore (id : ConstructorId) :
    ofCore id.toCore = id := by
  cases id
  simp [toCore, ofCore]

@[simp] theorem toCore_ofCore (id : Solcore.Core.ConstructorId) :
    toCore (ofCore id) = id := by
  cases id
  simp [toCore, ofCore]

end ConstructorId

inductive Ty where
  | unit
  | bool
  | word
  | product (left right : Ty)
  | function (parameter result : Ty)
  | sum (left right : Ty)
  | cell (elementType : Ty)
  | namedData (dataType : DataTypeId)
  deriving Repr, BEq, DecidableEq

structure DataDefinition where
  constructorPayloadTypes : List Ty
  deriving Repr, BEq, DecidableEq

abbrev DataEnvironment := List DataDefinition

inductive UnaryOp where
  | boolNot
  | wordNot
  | wordClz
  deriving Repr, BEq, DecidableEq

inductive BinaryOp where
  | wordAdd
  | wordSub
  | wordMul
  | wordDiv
  | wordMod
  | wordEq
  | wordGt
  | wordSgt
  | wordAnd
  | wordOr
  | wordXor
  | wordShl
  | wordShr
  | wordByte
  | wordSar
  | wordPow
  | wordSignExtend
  | wordSdiv
  | wordSmod
  deriving Repr, BEq, DecidableEq

inductive TernaryOp where
  | wordAddMod
  | wordMulMod
  deriving Repr, BEq, DecidableEq

inductive Expr where
  | unit
  | bool (value : Bool)
  | word (value : Solcore.Core.Word)
  | var (index : Nat)
  | pair (left right : Expr)
  | first (operand : Expr)
  | second (operand : Expr)
  | lambda (parameterType resultType : Ty) (body : Expr)
  | apply (function argument : Expr)
  | inLeft (rightType : Ty) (payload : Expr)
  | inRight (leftType : Ty) (payload : Expr)
  | caseE (scrutinee leftBranch rightBranch : Expr)
  | newCell (elementType : Ty) (initializer : Expr)
  | loadCell (reference : Expr)
  | storeCell (reference value : Expr)
  | construct (constructor : ConstructorId) (payload : Expr)
  | matchData
      (dataType : DataTypeId)
      (resultType : Ty)
      (scrutinee : Expr)
      (branches : List Expr)
  | unary (op : UnaryOp) (operand : Expr)
  | binary (op : BinaryOp) (left right : Expr)
  | ternary (op : TernaryOp) (first second third : Expr)
  | letE (initializer body : Expr)
  | ifE (condition thenBranch elseBranch : Expr)
  deriving Repr

structure Program where
  resultType : Ty
  dataDefinitions : DataEnvironment
  body : Expr
  deriving Repr

def schemaName : String := "solcore-semantic-core"

end Solcore.Core.Wire
