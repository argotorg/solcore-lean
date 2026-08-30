import Solcore.Abi.StaticWordMethodTable

/-! Consumers for deterministic Static Word method-table validation. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Semantics
open Solcore.Abi.V1

private def identityProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word (.var 0)
}

private def identityCode : CheckedHostCoreProgram :=
  ⟨identityProgram, by decide⟩

private def identityImplementation : WordImplementation :=
  ⟨identityCode, rfl, rfl⟩

private def incrementProgram : Program := {
  resultType := .function .word .word
  body := .lambda .word .word
    (.binary .wordAdd (.var 0) (.word ⟨1, by decide⟩))
}

private def incrementImplementation : WordImplementation :=
  ⟨⟨incrementProgram, by decide⟩, rfl, rfl⟩

private def name (text : String) (valid : isValidMethodName text = true) :
    MethodName :=
  ⟨text, valid⟩

private def method (methodName : MethodName) : Method where
  metadata := .staticWord methodName
  implementation := identityImplementation

private def methodWith
    (methodName : MethodName) (implementation : WordImplementation) : Method where
  metadata := .staticWord methodName
  implementation := implementation

private def fMethod : Method := method (name "f" (by decide))
private def fIncrementMethod : Method :=
  methodWith (name "f" (by decide)) incrementImplementation
private def fooMethod : Method := method (name "foo" (by decide))
private def collisionLow : Method := method (name "f116643" (by decide))
private def collisionHigh : Method := method (name "f38491" (by decide))

private structure ErrorSummary where
  kind : Nat
  firstSignature : String
  secondSignature : String
  selector : Nat
  deriving BEq, DecidableEq

private def summarizeError : MethodTableError → ErrorSummary
  | .empty => ⟨0, "", "", 0⟩
  | .duplicateSignature _ _ signature =>
      ⟨1, signature, signature, 0⟩
  | .selectorCollision _ _ first second selector =>
      ⟨2, first, second, selector.toUInt32.toNat⟩

private def summarizeResult
    (result : Except MethodTableError MethodTable) : ErrorSummary :=
  match result with
  | .error error => summarizeError error
  | .ok _ => ⟨3, "", "", 0⟩

private def duplicateSummary : ErrorSummary :=
  ⟨1, "f(uint256)", "f(uint256)", 0⟩

private def collisionSummary : ErrorSummary :=
  ⟨2, "f116643(uint256)", "f38491(uint256)", 0x77dbd42e⟩

private theorem compileTimeEmptyRejected :
    summarizeResult (MethodTable.validate []) = ⟨0, "", "", 0⟩ := by
  native_decide

private theorem compileTimeDuplicateNormalized :
    summarizeResult (MethodTable.validate [fMethod, fIncrementMethod]) =
      duplicateSummary ∧
    summarizeResult (MethodTable.validate [fIncrementMethod, fMethod]) =
      duplicateSummary := by
  native_decide

private theorem compileTimeKnownCollision :
    collisionLow.metadata.selector.toUInt32.toNat = 0x77dbd42e ∧
      collisionHigh.metadata.selector.toUInt32.toNat = 0x77dbd42e := by
  native_decide

private theorem compileTimeCollisionNormalized :
    summarizeResult
        (MethodTable.validate [collisionHigh, collisionLow]) =
      collisionSummary ∧
    summarizeResult
        (MethodTable.validate [collisionLow, collisionHigh]) =
      collisionSummary := by
  native_decide

private def acceptedSignatures (methods : List Method) : Option (List String) :=
  match MethodTable.validate methods with
  | .error _ => none
  | .ok table => some (table.entries.map IndexedMethod.signature)

private theorem compileTimeDistinctAccepted :
    acceptedSignatures [fooMethod, fMethod] =
      some ["f(uint256)", "foo(uint256)"] := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testAbiStaticWordMethodTable : IO Unit := do
  assertTrue
    (summarizeResult (MethodTable.validate []) == ⟨0, "", "", 0⟩)
    "an empty Static Word method table must be rejected"
  let duplicateForward := summarizeResult
    (MethodTable.validate [fMethod, fIncrementMethod])
  let duplicateReverse := summarizeResult
    (MethodTable.validate [fIncrementMethod, fMethod])
  assertTrue
    (duplicateForward == duplicateSummary &&
      duplicateReverse == duplicateSummary)
    "duplicate signatures must produce one normalized error"
  let collisionForward := summarizeResult
    (MethodTable.validate [collisionHigh, collisionLow])
  let collisionReverse := summarizeResult
    (MethodTable.validate [collisionLow, collisionHigh])
  assertTrue
    (collisionForward == collisionSummary &&
      collisionReverse == collisionSummary)
    "selector collisions must retain their canonical signatures and selector"
  assertTrue
    (acceptedSignatures [fooMethod, fMethod] ==
      some ["f(uint256)", "foo(uint256)"])
    "distinct methods must produce a nonempty canonical table"

end Tests
