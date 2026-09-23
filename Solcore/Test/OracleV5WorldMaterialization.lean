import Solcore.Oracle.V5.WorldMaterialization

/-! Executable regressions for Oracle v5 finite-world materialization. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.ContractRuntime

private def addressA : Address := ⟨1, by decide⟩
private def addressB : Address := ⟨2, by decide⟩
private def addressC : Address := ⟨3, by decide⟩

private def slot1 : Word := ⟨11, by decide⟩
private def slot2 : Word := ⟨12, by decide⟩
private def value1 : Word := ⟨21, by decide⟩
private def value2 : Word := ⟨22, by decide⟩
private def balance : Word := ⟨31, by decide⟩
private def nonce : Word := ⟨41, by decide⟩

private def program : Program := {
  resultType := .word
  dataDefinitions := []
  body := .word value1
}

private theorem programChecked : program.checkHost = true := by decide

private def code : CheckedHostCoreProgram :=
  ⟨program, programChecked⟩

private def resolveCode : String → Option CheckedHostCoreProgram
  | "counter" => some code
  | _ => none

private def emptyAccountAtA : AccountInput := {
  address := addressA
  balance := Word.zero
  nonce := Word.zero
  storage := []
  code := none
}

private def populatedAccountAtB : AccountInput := {
  address := addressB
  balance
  nonce
  storage := [
    { slot := slot2, value := value2 },
    { slot := slot1, value := value1 }
  ]
  code := some "counter"
}

private def input : WorldInput := {
  accounts := [populatedAccountAtB, emptyAccountAtA]
}

private def reorderedInput : WorldInput := {
  accounts := [
    emptyAccountAtA,
    { populatedAccountAtB with storage := populatedAccountAtB.storage.reverse }
  ]
}

private def storageValue?
    (state : WorldState)
    (address : Address)
    (slot : Word) : Option Word := do
  let account ← state.account? address
  account.storageValue? slot

private def codeProgram?
    (state : WorldState)
    (address : Address) : Option Program := do
  let account ← state.account? address
  let installed ← account.code?
  some installed.program

private structure WorldSnapshot where
  aPresent : Bool
  bPresent : Bool
  cPresent : Bool
  aBalance : Option Word
  bBalance : Option Word
  bNonce : Option Word
  bSlot1 : Option Word
  bSlot2 : Option Word
  bMissingSlot : Option Word
  bCode : Option Program
  deriving BEq

private def snapshot (state : WorldState) : WorldSnapshot := {
  aPresent := (state.account? addressA).isSome
  bPresent := (state.account? addressB).isSome
  cPresent := (state.account? addressC).isSome
  aBalance := state.balance? addressA
  bBalance := state.balance? addressB
  bNonce := state.nonce? addressB
  bSlot1 := storageValue? state addressB slot1
  bSlot2 := storageValue? state addressB slot2
  bMissingSlot := storageValue? state addressB Word.zero
  bCode := codeProgram? state addressB
}

private def expectedSnapshot : WorldSnapshot := {
  aPresent := true
  bPresent := true
  cPresent := false
  aBalance := some Word.zero
  bBalance := some balance
  bNonce := some nonce
  bSlot1 := some value1
  bSlot2 := some value2
  bMissingSlot := none
  bCode := some program
}

private def successfulAndOrderIndependent : Bool :=
  match WorldMaterialization.materializeWith resolveCode input,
      WorldMaterialization.materializeWith resolveCode reorderedInput with
  | .ok first, .ok second =>
      snapshot first == expectedSnapshot && snapshot first == snapshot second
  | _, _ => false

private def failure?
    (world : WorldInput) : Option WorldMaterializationError :=
  match WorldMaterialization.materializeWith resolveCode world with
  | .ok _ => none
  | .error failure => some failure

private def duplicateAccountRejectedFirst : Bool :=
  failure? {
    accounts := [
      { populatedAccountAtB with
        storage := [
          { slot := slot1, value := Word.zero },
          { slot := slot1, value := Word.zero }
        ]
        code := some "missing"
      },
      emptyAccountAtA,
      { emptyAccountAtA with code := some "missing" }
    ]
  } == some (.duplicateAccount addressA)

private def duplicateStorageRejectedBeforeZero : Bool :=
  failure? {
    accounts := [{ populatedAccountAtB with
      storage := [
        { slot := slot1, value := value1 },
        { slot := slot1, value := Word.zero }
      ]
      code := some "missing"
    }]
  } == some (.duplicateStorageSlot addressB slot1)

private def zeroStorageRejectedBeforeDangling : Bool :=
  failure? {
    accounts := [{ populatedAccountAtB with
      storage := [{ slot := slot2, value := Word.zero }]
      code := some "missing"
    }]
  } == some (.zeroStorageValue addressB slot2)

private def danglingCodeRejected : Bool :=
  failure? {
    accounts := [{ populatedAccountAtB with code := some "missing" }]
  } == some (.danglingContract addressB "missing")

private theorem canonicalOrderIsExact :
    (WorldMaterialization.canonicalAccounts input.accounts).map
      (fun account => account.address) = [addressA, addressB] ∧
    (WorldMaterialization.canonicalStorage populatedAccountAtB.storage).map
      (fun entry => entry.slot) = [slot1, slot2] := by
  native_decide

private theorem compileTimeWorldMaterializationRegressions :
    successfulAndOrderIndependent = true ∧
      duplicateAccountRejectedFirst = true ∧
      duplicateStorageRejectedBeforeZero = true ∧
      zeroStorageRejectedBeforeDangling = true ∧
      danglingCodeRejected = true := by
  native_decide

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def testOracleV5WorldMaterialization : IO Unit := do
  assertTrue successfulAndOrderIndependent
    "Oracle v5 finite-world materialization lost data or depends on input order"
  assertTrue duplicateAccountRejectedFirst
    "duplicate Account validation did not take canonical precedence"
  assertTrue duplicateStorageRejectedBeforeZero
    "duplicate storage validation did not precede zero-value validation"
  assertTrue zeroStorageRejectedBeforeDangling
    "zero storage validation did not precede dangling-code validation"
  assertTrue danglingCodeRejected
    "dangling Account code was not rejected with its exact identity"

end Tests
