import Solcore.Oracle.V5.RootInstallation

/-! Focused executable regressions for Oracle v5 root installation. -/

set_option autoImplicit false

namespace Tests.OracleV5RootInstallation

open Solcore.Core.Wire
open Solcore.Oracle.V5
open Solcore.Oracle.V5.ContractAdmission
open Solcore.ContractRuntime

private def zero : Solcore.Core.Word := ⟨0, by decide⟩
private def one : Solcore.Core.Word := ⟨1, by decide⟩

private def returnProgram (value : Solcore.Core.Word) : V3.Program := {
  resultType := .word
  dataDefinitions := []
  body := .word value
}

private def outcomeProgram : V3.Program := {
  resultType := .sum .word (.sum .word .word)
  dataDefinitions := []
  body := .inLeft (.sum .word .word) (.word zero)
}

private def raw (id : String) (program : V3.Program) : ContractInput := {
  id
  spec := .checkedCore program
}

private def returnTarget : Address := ⟨1, by decide⟩
private def outcomeTarget : Address := ⟨2, by decide⟩
private def emptyTarget : Address := ⟨3, by decide⟩
private def absentTarget : Address := ⟨4, by decide⟩

private def account
    (address : Address)
    (code : Option String) : AccountInput := {
  address
  balance := zero
  nonce := zero
  storage := []
  code
}

private def contracts : List ContractInput := [
  raw "return" (returnProgram zero),
  raw "outcome" outcomeProgram
]

private def worldInput : WorldInput := {
  accounts := [
    account returnTarget (some "return"),
    account outcomeTarget (some "outcome"),
    account emptyTarget none
  ]
}

private def installedProfilesExact : Bool :=
  match ContractAdmission.admit contracts with
  | .error _ => false
  | .ok package =>
      match WorldMaterialization.materializeWith package.codeResolver
          worldInput with
      | .error _ => false
      | .ok world =>
          match RootInstallation.install package world returnTarget,
              RootInstallation.install package world outcomeTarget with
          | .installed returned, .installed outcome =>
              returned.contractId.value == "return" &&
                returned.contract.entryProfile == .returnWord &&
                outcome.contractId.value == "outcome" &&
                outcome.contract.entryProfile == .wordOutcomeV1 &&
                package.codeIdResolver returned.contract.code.program ==
                  some returned.contractId &&
                package.codeIdResolver outcome.contract.code.program ==
                  some outcome.contractId &&
                (package.contractResolver "return").isSome &&
                (package.codeResolver "outcome").isSome
          | _, _ => false

private theorem installedProfilesExact_proved :
    installedProfilesExact = true := by
  native_decide

private inductive RootSummary where
  | installed
  | targetAbsent
  | targetCodeAbsent
  | internal (error : InternalError)
  deriving Repr, BEq, DecidableEq

private def summarize
    {package : ContractPackage}
    {world : WorldState}
    {target : Address}
    (result : RootInstallationResult package world target) : RootSummary :=
  match result with
  | .installed _ => .installed
  | .rejected .targetAbsent => .targetAbsent
  | .rejected .targetCodeAbsent => .targetCodeAbsent
  | .internalError error => .internal error

private def semanticRejectionsExact : Bool :=
  match ContractAdmission.admit contracts with
  | .error _ => false
  | .ok package =>
      match WorldMaterialization.materializeWith package.codeResolver
          worldInput with
      | .error _ => false
      | .ok world =>
          summarize (RootInstallation.install package world absentTarget) ==
              .targetAbsent &&
            summarize (RootInstallation.install package world emptyTarget) ==
              .targetCodeAbsent

private theorem semanticRejectionsExact_proved :
    semanticRejectionsExact = true := by
  native_decide

/-- Successful values expose every proof required by balanced execution. -/
private theorem installedCarriesExactEvidence
    {package : ContractPackage}
    {world : WorldState}
    {target : Address}
    (root : InstalledRoot package world target) :
    package.lookup? root.contractId = some root.contract ∧
      world.account? target = some root.installed.account ∧
      root.installed.account.code? = some root.contract.code :=
  ⟨root.packageLookup, root.installed.account_present,
    root.installed.code_present⟩

private def foreignProgram : Solcore.Core.Program :=
  (returnProgram one).toCore

private theorem foreignProgram_checked : foreignProgram.checkHost = true := by
  native_decide

private def foreignCode : CheckedHostCoreProgram :=
  ⟨foreignProgram, foreignProgram_checked⟩

private def foreignWorld : WorldState :=
  WorldState.empty.putAccount returnTarget
    (Account.empty.withCode foreignCode)

private def sameProgramWorld : WorldState :=
  WorldState.empty.putAccount returnTarget
    (Account.empty.withCode
      ⟨(returnProgram zero).toCore, by native_decide⟩)

private def separatelyWrappedSameProgramSucceeds : Bool :=
  match ContractAdmission.admit [raw "return" (returnProgram zero)] with
  | .error _ => false
  | .ok package =>
      match RootInstallation.install package sameProgramWorld returnTarget with
      | .installed root =>
          root.contractId.value == "return" &&
            root.contract.entryProfile == .returnWord
      | _ => false

private theorem separatelyWrappedSameProgramSucceeds_proved :
    separatelyWrappedSameProgramSucceeds = true := by
  native_decide

private def foreignCodeIsInternal : Bool :=
  match ContractAdmission.admit [raw "return" (returnProgram zero)] with
  | .error _ => false
  | .ok package =>
      summarize
        (RootInstallation.install package foreignWorld returnTarget) ==
          .internal .worldCodeReferenceInvariant

private theorem foreignCodeIsInternal_proved :
    foreignCodeIsInternal = true := by
  native_decide

private def allChecks : Bool :=
  installedProfilesExact && semanticRejectionsExact &&
    separatelyWrappedSameProgramSucceeds && foreignCodeIsInternal

private theorem allChecks_proved : allChecks = true := by
  native_decide

def testOracleV5RootInstallation : IO Unit := do
  unless allChecks do
    throw (IO.userError "Oracle v5 root installation regression failed")

end Tests.OracleV5RootInstallation
