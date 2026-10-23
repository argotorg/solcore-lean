import Solcore.Frontend.RustHull.Syntax
import Solcore.Core.LocalLoop
import Solcore.Core.Check

/-! Shared state for lowering imported Hull into ordinary Core expressions. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull

structure LoweringError where
  message : String
  span : Option Span := none
  deriving Repr

abbrev LowerM := Except LoweringError

def fail {α : Type} (message : String) (span : Option Span := none) : LowerM α :=
  .error ⟨message, span⟩

structure Lowered where
  type : Core.Ty
  /-- An ordinary Core computation returning `LanguageResult.resultType type`. -/
  expression : Core.Expr
  deriving Repr

structure Binding where
  name : Option String
  type : Core.Ty
  reference : Bool := true
  deriving Repr

abbrev Scope := List Binding

namespace Scope

def temporary (scope : Scope) (type : Core.Ty := .unit) : Scope :=
  ⟨none, type, false⟩ :: scope

def addLocal (scope : Scope) (name : String) (type : Core.Ty) : Scope :=
  ⟨some name, type, true⟩ :: scope

def lookup (scope : Scope) (name : String) : LowerM (Binding × Nat) :=
  match scope.zipIdx.find? (fun item => item.1.name == some name) with
  | some binding => pure binding
  | none => fail s!"unknown binding: {name}"

def read (scope : Scope) (name : String) : LowerM Lowered := do
  let (binding, index) ← scope.lookup name
  pure ⟨binding.type, if binding.reference then
    Core.OptionalCell.read binding.type (.var index) (Core.Word.ofNatModulo 1)
    else Core.LanguageResult.success (.var index)⟩

end Scope

def expectType (expected actual : Core.Ty) : LowerM Unit :=
  if expected = actual then pure ()
  else fail s!"type mismatch: expected {reprStr expected}, received {reprStr actual}"

/-- Hull's arbitrary-width nonnegative literals are reduced modulo 2^256. -/
def parseWord (text : String) : LowerM Core.Word := do
  let chars := text.toList
  let (base, digits) := match chars with
    | '0' :: 'x' :: digits | '0' :: 'X' :: digits => (16, digits)
    | _ => (10, chars)
  if digits.isEmpty then fail s!"empty word literal: {text}"
  else
    let value ← digits.foldlM (fun accumulator char => do
      let digit := if '0' ≤ char && char ≤ '9' then char.toNat - '0'.toNat
        else if 'a' ≤ char && char ≤ 'f' then char.toNat - 'a'.toNat + 10
        else if 'A' ≤ char && char ≤ 'F' then char.toNat - 'A'.toNat + 10
        else base
      if digit < base then pure ((accumulator * base + digit) % Core.wordModulus)
      else fail s!"invalid word literal: {text}") 0
    pure (Core.Word.ofNatModulo value)

/-- Transparent named layouts are expanded here; recursive references need the
named-data layout pass and are rejected until that pass is available. -/
def lowerType : Nat → Ty → LowerM Core.Ty
  | 0, _ => fail "type expansion depth exhausted"
  | fuel + 1, type => match type with
    | .word => pure .word
    | .bool => pure .bool
    | .unit => pure .unit
    | .product left right => return .product (← lowerType fuel left) (← lowerType fuel right)
    | .sum left right => return .sum (← lowerType fuel left) (← lowerType fuel right)
    | .named _ inner | .located _ inner => lowerType fuel inner
    | .namedRef name => fail s!"recursive named layout is not implemented: {name}"
    | .function _ _ => fail "residual Hull function type requires closure conversion"

def bundleType : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: rest => .product type (bundleType rest)

def bundle : List Core.Expr → Core.Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (bundle rest)

def projectArgument (index : Nat) : Nat → Core.Expr → Core.Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
    else projectArgument (index - 1) (count + 1) (.second value)

def packArguments : List Lowered → Lowered
  | [] => ⟨.unit, Core.LanguageResult.success .unit⟩
  | [value] => value
  | value :: rest =>
      let tail := packArguments rest
      ⟨.product value.type tail.type,
        Core.LocalSequence.pair value.type tail.type value.expression tail.expression⟩

/-- Hull/Yul local allocation starts with zero words, including sum tag zero. -/
def zeroValue : Core.Ty → LowerM Core.Expr
  | .word => pure (.word Core.Word.zero)
  | .bool => pure (.bool false)
  | .unit => pure .unit
  | .product left right => return .pair (← zeroValue left) (← zeroValue right)
  | .sum left right => return .inLeft right (← zeroValue left)
  | _ => fail "no finite zero layout for this local type"

structure Signature where
  name : String
  parameters : List Core.Ty
  result : Core.Ty
  deriving Repr

def Signature.functionType (signature : Signature) : Core.Ty :=
  .function (bundleType signature.parameters) (Core.LanguageResult.resultType signature.result)

end Solcore.Frontend.RustHull
