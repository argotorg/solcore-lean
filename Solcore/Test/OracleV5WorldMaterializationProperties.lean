import Solcore.Oracle.V5.WorldMaterialization

/-! External-consumer checks for finite-world materialization laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Core
open Solcore.Oracle.V5
open Solcore.ContractRuntime

private def presentAddress : Address := ⟨1, by decide⟩
private def absentAddress : Address := ⟨2, by decide⟩
private def balance : Word := ⟨11, by decide⟩
private def nonce : Word := ⟨12, by decide⟩
private def slot : Word := ⟨21, by decide⟩
private def value : Word := ⟨22, by decide⟩

private def inputAccount : AccountInput := {
  address := presentAddress
  balance
  nonce
  storage := [{ slot, value }]
  code := none
}

private def inputWorld : WorldInput := {
  accounts := [inputAccount]
}

private def resolveCode : String → Option CheckedHostCoreProgram :=
  fun _ => none

private theorem selectedInput :
    WorldMaterialization.accountInput? inputWorld presentAddress =
      some inputAccount := by
  native_decide

private theorem absentInput :
    WorldMaterialization.accountInput? inputWorld absentAddress = none := by
  native_decide

private theorem exactWorldProvenance
    (state : WorldState)
    (success :
      WorldMaterialization.materializeWith resolveCode inputWorld = .ok state) :
    state.balance? presentAddress = some balance ∧
    state.nonce? presentAddress = some nonce ∧
    (state.account? presentAddress).bind
        (fun account => account.storageValue? slot) = some value ∧
    (state.account? presentAddress).bind Account.code? = none ∧
    state.account? absentAddress = none := by
  constructor
  · exact WorldMaterialization.balance?_of_input resolveCode inputWorld
      state success presentAddress inputAccount
      selectedInput
  constructor
  · exact WorldMaterialization.nonce?_of_input resolveCode inputWorld
      state success presentAddress inputAccount
      selectedInput
  constructor
  · calc
      (state.account? presentAddress).bind
          (fun account => account.storageValue? slot) =
          WorldMaterialization.storageValueOf inputAccount slot :=
        WorldMaterialization.storageValue?_of_input resolveCode inputWorld
          state success presentAddress inputAccount
          selectedInput slot
      _ = some value := by native_decide
  constructor
  · exact WorldMaterialization.code?_of_input resolveCode inputWorld
      state success presentAddress inputAccount selectedInput
  · exact WorldMaterialization.account?_eq_none_of_input_absent resolveCode
      inputWorld state success absentAddress absentInput

def testOracleV5WorldMaterializationProperties : IO Unit := do
  let _ := exactWorldProvenance
  pure ()

end Tests
