import Solcore.Core.Wire.Syntax

/-! Total Wire-to-Core maps and selectively defined Core-to-Wire projections. -/

set_option autoImplicit false

namespace Solcore.Core.Wire

namespace Ty

def toCore : Ty → Solcore.Core.Ty
  | .unit => .unit
  | .bool => .bool
  | .word => .word
  | .integer => .integer
  | .product left right => .product left.toCore right.toCore
  | .function parameter result => .function parameter.toCore result.toCore
  | .sum left right => .sum left.toCore right.toCore
  | .cell elementType => .cell elementType.toCore
  | .namedData dataType => .namedData dataType.toCore

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.Ty → Option Ty
  | .unit => some .unit
  | .bool => some .bool
  | .word => some .word
  | .integer => some .integer
  | .product left right => return .product (← ofCore? left) (← ofCore? right)
  | .function parameter result =>
      return .function (← ofCore? parameter) (← ofCore? result)
  | .sum left right => return .sum (← ofCore? left) (← ofCore? right)
  | .cell elementType => return .cell (← ofCore? elementType)
  | .namedData dataType => some (.namedData (.ofCore dataType))
  | _ => none

@[simp] theorem ofCore?_toCore (type : Ty) :
    ofCore? type.toCore = some type := by
  induction type <;> simp_all [toCore, ofCore?]

theorem toCore_injective : Function.Injective toCore := by
  intro left right equality
  have := congrArg ofCore? equality
  simpa using this

end Ty

namespace DataDefinition

private theorem mapM_ofCore?_toCore (types : List Ty) :
    types.mapM (Ty.ofCore? ∘ Ty.toCore) = some types := by
  induction types with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, ih]

def toCore (definition : DataDefinition) : Solcore.Core.DataDefinition := {
  constructorPayloadTypes :=
    definition.constructorPayloadTypes.map Ty.toCore
}

def ofCore? (definition : Solcore.Core.DataDefinition) : Option DataDefinition := do
  let payloadTypes ← definition.constructorPayloadTypes.mapM Ty.ofCore?
  some { constructorPayloadTypes := payloadTypes }

@[simp] theorem ofCore?_toCore (definition : DataDefinition) :
    ofCore? definition.toCore = some definition := by
  cases definition
  simp only [toCore, ofCore?]
  rw [List.mapM_map, mapM_ofCore?_toCore]
  rfl

end DataDefinition

namespace UnaryOp

def toCore : UnaryOp → Solcore.Core.UnaryOp
  | .boolNot => .boolNot
  | .wordNot => .wordNot
  | .wordClz => .wordClz
  | .integerNot => .integerNot
  | .integerToWord => .integerToWord
  | .wordToInteger => .wordToInteger

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.UnaryOp → Option UnaryOp
  | .boolNot => some .boolNot
  | .wordNot => some .wordNot
  | .wordClz => some .wordClz
  | .integerNot => some .integerNot
  | .integerToWord => some .integerToWord
  | .wordToInteger => some .wordToInteger
  | _ => none

@[simp] theorem ofCore?_toCore (op : UnaryOp) :
    ofCore? op.toCore = some op := by
  cases op <;> rfl

end UnaryOp

namespace BinaryOp

def toCore : BinaryOp → Solcore.Core.BinaryOp
  | .wordAdd => .wordAdd
  | .wordSub => .wordSub
  | .wordMul => .wordMul
  | .wordDiv => .wordDiv
  | .wordMod => .wordMod
  | .wordEq => .wordEq
  | .wordGt => .wordGt
  | .wordSgt => .wordSgt
  | .wordAnd => .wordAnd
  | .wordOr => .wordOr
  | .wordXor => .wordXor
  | .wordShl => .wordShl
  | .wordShr => .wordShr
  | .wordByte => .wordByte
  | .wordSar => .wordSar
  | .wordPow => .wordPow
  | .wordSignExtend => .wordSignExtend
  | .wordSdiv => .wordSdiv
  | .wordSmod => .wordSmod
  | .integerAdd => .integerAdd
  | .integerSub => .integerSub
  | .integerMul => .integerMul
  | .integerDiv => .integerDiv
  | .integerMod => .integerMod
  | .integerEq => .integerEq
  | .integerLt => .integerLt
  | .integerAnd => .integerAnd
  | .integerOr => .integerOr
  | .integerXor => .integerXor

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.BinaryOp → Option BinaryOp
  | .wordAdd => some .wordAdd
  | .wordSub => some .wordSub
  | .wordMul => some .wordMul
  | .wordDiv => some .wordDiv
  | .wordMod => some .wordMod
  | .wordEq => some .wordEq
  | .wordGt => some .wordGt
  | .wordSgt => some .wordSgt
  | .wordAnd => some .wordAnd
  | .wordOr => some .wordOr
  | .wordXor => some .wordXor
  | .wordShl => some .wordShl
  | .wordShr => some .wordShr
  | .wordByte => some .wordByte
  | .wordSar => some .wordSar
  | .wordPow => some .wordPow
  | .wordSignExtend => some .wordSignExtend
  | .wordSdiv => some .wordSdiv
  | .wordSmod => some .wordSmod
  | .integerAdd => some .integerAdd
  | .integerSub => some .integerSub
  | .integerMul => some .integerMul
  | .integerDiv => some .integerDiv
  | .integerMod => some .integerMod
  | .integerEq => some .integerEq
  | .integerLt => some .integerLt
  | .integerAnd => some .integerAnd
  | .integerOr => some .integerOr
  | .integerXor => some .integerXor
  | _ => none

@[simp] theorem ofCore?_toCore (op : BinaryOp) :
    ofCore? op.toCore = some op := by
  cases op <;> rfl

end BinaryOp

namespace TernaryOp

def toCore : TernaryOp → Solcore.Core.TernaryOp
  | .wordAddMod => .wordAddMod
  | .wordMulMod => .wordMulMod

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.TernaryOp → Option TernaryOp
  | .wordAddMod => some .wordAddMod
  | .wordMulMod => some .wordMulMod
  | _ => none

@[simp] theorem ofCore?_toCore (op : TernaryOp) :
    ofCore? op.toCore = some op := by
  cases op <;> rfl

end TernaryOp

namespace Expr

def toCore : Expr → Solcore.Core.Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .var index => .var index
  | .pair left right => .pair left.toCore right.toCore
  | .first operand => .first operand.toCore
  | .second operand => .second operand.toCore
  | .lambda parameterType resultType body =>
      .lambda parameterType.toCore resultType.toCore body.toCore
  | .apply function argument => .apply function.toCore argument.toCore
  | .inLeft rightType payload => .inLeft rightType.toCore payload.toCore
  | .inRight leftType payload => .inRight leftType.toCore payload.toCore
  | .caseE scrutinee leftBranch rightBranch =>
      .caseE scrutinee.toCore leftBranch.toCore rightBranch.toCore
  | .newCell elementType initializer =>
      .newCell elementType.toCore initializer.toCore
  | .loadCell reference => .loadCell reference.toCore
  | .storeCell reference value => .storeCell reference.toCore value.toCore
  | .construct constructor payload =>
      .construct constructor.toCore payload.toCore
  | .matchData dataType resultType scrutinee branches =>
      .matchData dataType.toCore resultType.toCore scrutinee.toCore
        (branches.map toCore)
  | .unary op operand => .unary op.toCore operand.toCore
  | .binary op left right => .binary op.toCore left.toCore right.toCore
  | .ternary op firstOperand secondOperand thirdOperand =>
      .ternary op.toCore firstOperand.toCore secondOperand.toCore
        thirdOperand.toCore
  | .letE initializer body => .letE initializer.toCore body.toCore
  | .ifE condition thenBranch elseBranch =>
      .ifE condition.toCore thenBranch.toCore elseBranch.toCore
termination_by expression => sizeOf expression

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.Expr → Option Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .var index => some (.var index)
  | .pair left right => return .pair (← ofCore? left) (← ofCore? right)
  | .first operand => return .first (← ofCore? operand)
  | .second operand => return .second (← ofCore? operand)
  | .lambda parameterType resultType body =>
      return .lambda (← Ty.ofCore? parameterType) (← Ty.ofCore? resultType)
        (← ofCore? body)
  | .apply function argument =>
      return .apply (← ofCore? function) (← ofCore? argument)
  | .inLeft rightType payload =>
      return .inLeft (← Ty.ofCore? rightType) (← ofCore? payload)
  | .inRight leftType payload =>
      return .inRight (← Ty.ofCore? leftType) (← ofCore? payload)
  | .caseE scrutinee leftBranch rightBranch =>
      return .caseE (← ofCore? scrutinee) (← ofCore? leftBranch)
        (← ofCore? rightBranch)
  | .newCell elementType initializer =>
      return .newCell (← Ty.ofCore? elementType) (← ofCore? initializer)
  | .loadCell reference => return .loadCell (← ofCore? reference)
  | .storeCell reference value =>
      return .storeCell (← ofCore? reference) (← ofCore? value)
  | .construct constructor payload =>
      return .construct (.ofCore constructor) (← ofCore? payload)
  | .matchData dataType resultType scrutinee branches =>
      return .matchData (.ofCore dataType) (← Ty.ofCore? resultType)
        (← ofCore? scrutinee) (← branches.mapM ofCore?)
  | .unary op operand =>
      return .unary (← UnaryOp.ofCore? op) (← ofCore? operand)
  | .binary op left right =>
      return .binary (← BinaryOp.ofCore? op) (← ofCore? left) (← ofCore? right)
  | .ternary op firstOperand secondOperand thirdOperand =>
      return .ternary (← TernaryOp.ofCore? op) (← ofCore? firstOperand)
        (← ofCore? secondOperand) (← ofCore? thirdOperand)
  | .letE initializer body =>
      return .letE (← ofCore? initializer) (← ofCore? body)
  | .ifE condition thenBranch elseBranch =>
      return .ifE (← ofCore? condition) (← ofCore? thenBranch)
        (← ofCore? elseBranch)
  | _ => none
termination_by expression => sizeOf expression

mutual

  @[simp] theorem ofCore?_toCore : (expression : Expr) →
      ofCore? expression.toCore = some expression
    | .unit => by simp [toCore, ofCore?]
    | .bool _ => by simp [toCore, ofCore?]
    | .word _ => by simp [toCore, ofCore?]
    | .integer _ => by simp [toCore, ofCore?]
    | .var _ => by simp [toCore, ofCore?]
    | .pair left right => by
        simp [toCore, ofCore?, ofCore?_toCore left, ofCore?_toCore right]
    | .first operand => by
        simp [toCore, ofCore?, ofCore?_toCore operand]
    | .second operand => by
        simp [toCore, ofCore?, ofCore?_toCore operand]
    | .lambda parameterType resultType body => by
        simp [toCore, ofCore?, ofCore?_toCore body]
    | .apply function argument => by
        simp [toCore, ofCore?, ofCore?_toCore function,
          ofCore?_toCore argument]
    | .inLeft rightType payload => by
        simp [toCore, ofCore?, ofCore?_toCore payload]
    | .inRight leftType payload => by
        simp [toCore, ofCore?, ofCore?_toCore payload]
    | .caseE scrutinee leftBranch rightBranch => by
        simp [toCore, ofCore?, ofCore?_toCore scrutinee,
          ofCore?_toCore leftBranch, ofCore?_toCore rightBranch]
    | .newCell elementType initializer => by
        simp [toCore, ofCore?, ofCore?_toCore initializer]
    | .loadCell reference => by
        simp [toCore, ofCore?, ofCore?_toCore reference]
    | .storeCell reference value => by
        simp [toCore, ofCore?, ofCore?_toCore reference,
          ofCore?_toCore value]
    | .construct constructor payload => by
        simp [toCore, ofCore?, ofCore?_toCore payload]
    | .matchData dataType resultType scrutinee branches => by
        simp [toCore, ofCore?, ofCore?_toCore scrutinee,
          mapM_ofCore?_map_toCore branches]
    | .unary op operand => by
        simp [toCore, ofCore?, ofCore?_toCore operand]
    | .binary op left right => by
        simp [toCore, ofCore?, ofCore?_toCore left, ofCore?_toCore right]
    | .ternary op firstOperand secondOperand thirdOperand => by
        simp [toCore, ofCore?, ofCore?_toCore firstOperand,
          ofCore?_toCore secondOperand, ofCore?_toCore thirdOperand]
    | .letE initializer body => by
        simp [toCore, ofCore?, ofCore?_toCore initializer,
          ofCore?_toCore body]
    | .ifE condition thenBranch elseBranch => by
        simp [toCore, ofCore?, ofCore?_toCore condition,
          ofCore?_toCore thenBranch, ofCore?_toCore elseBranch]

  @[simp] theorem mapM_ofCore?_map_toCore : (expressions : List Expr) →
      (expressions.map toCore).mapM ofCore? = some expressions
    | [] => rfl
    | head :: tail => by
        simp [List.mapM_cons, ofCore?_toCore head,
          mapM_ofCore?_map_toCore tail]

end

theorem toCore_injective : Function.Injective toCore := by
  intro left right equality
  have projected := congrArg ofCore? equality
  simpa using projected

instance : DecidableEq Expr := fun left right =>
  if equality : left.toCore = right.toCore then
    isTrue (toCore_injective equality)
  else
    isFalse fun wireEquality => equality (congrArg toCore wireEquality)

instance : BEq Expr :=
  ⟨fun left right => decide (left = right)⟩

instance : LawfulBEq Expr where
  rfl := by
    intro expression
    change decide (expression = expression) = true
    exact of_decide_eq_self_eq_true expression
  eq_of_beq := by
    intro left right equality
    change decide (left = right) = true at equality
    exact of_decide_eq_true equality

end Expr

namespace Program

def toCore (program : Program) : Solcore.Core.Program := {
  resultType := program.resultType.toCore
  dataDefinitions := program.dataDefinitions.map DataDefinition.toCore
  body := program.body.toCore
}

def ofCore? (program : Solcore.Core.Program) : Option Program := do
  let resultType ← Ty.ofCore? program.resultType
  let dataDefinitions ← program.dataDefinitions.mapM DataDefinition.ofCore?
  let body ← Expr.ofCore? program.body
  some { resultType, dataDefinitions, body }

private theorem mapM_ofCore?_map_toCore (definitions : DataEnvironment) :
    definitions.mapM
        (DataDefinition.ofCore? ∘ DataDefinition.toCore) = some definitions := by
  induction definitions with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, ih]

@[simp] theorem ofCore?_toCore (program : Program) :
    ofCore? program.toCore = some program := by
  cases program
  simp only [toCore, ofCore?, Ty.ofCore?_toCore, Expr.ofCore?_toCore,
    List.mapM_map]
  rw [mapM_ofCore?_map_toCore]
  rfl

theorem toCore_injective : Function.Injective toCore := by
  intro left right equality
  have projected := congrArg ofCore? equality
  simpa using projected

instance : DecidableEq Program := fun left right =>
  if equality : left.toCore = right.toCore then
    isTrue (toCore_injective equality)
  else
    isFalse fun wireEquality => equality (congrArg toCore wireEquality)

instance : BEq Program :=
  ⟨fun left right => decide (left = right)⟩

instance : LawfulBEq Program where
  rfl := by
    intro program
    change decide (program = program) = true
    exact of_decide_eq_self_eq_true program
  eq_of_beq := by
    intro left right equality
    change decide (left = right) = true at equality
    exact of_decide_eq_true equality

end Program

end Solcore.Core.Wire
