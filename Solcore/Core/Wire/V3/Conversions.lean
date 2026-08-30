import Solcore.Core.Wire.V3.Syntax

/-! Total v3-to-Core maps and closed, partial Core-to-v3 projections. -/

set_option autoImplicit false

namespace Solcore.Core.Wire.V3

namespace Ty

def toCore : Ty → Solcore.Core.Ty
  | .unit => .unit
  | .bool => .bool
  | .word => .word
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

set_option match.ignoreUnusedAlts true in
def ofCore? : Solcore.Core.UnaryOp → Option UnaryOp
  | .boolNot => some .boolNot
  | .wordNot => some .wordNot
  | .wordClz => some .wordClz
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

end Solcore.Core.Wire.V3
