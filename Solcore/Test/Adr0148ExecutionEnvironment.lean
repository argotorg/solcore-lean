import Solcore.ContractRuntime.CheckedCreationTemplateRegistry
import Solcore.ContractRuntime.ExecutionEnvironment
import Solcore.Test.TopLevelExecutionFixture

/-! External and executable checks for the immutable creation environment. -/

set_option autoImplicit false

namespace Tests.Adr0148ExecutionEnvironment

open Solcore.Core
open Solcore.ContractRuntime
open Tests.TopLevelExecutionFixture

example := CheckedCreationTemplate.mk_initializer
example := CheckedCreationTemplate.mk_runtime
example := CheckedCreationTemplateRegistry.empty_lookup
example := ExecutionEnvironment.callsOnly_callRegistry
example := ExecutionEnvironment.callsOnly_creationTemplates_lookup
example := ExecutionEnvironment.inertCreationAddressPolicy_derive
example := ExecutionEnvironment.callsOnly_creationAddressPolicy_derive

private def identifier : Word := ⟨0x48, by decide⟩
private def otherIdentifier : Word := ⟨0x49, by decide⟩
private def template : CheckedCreationTemplate := {
  initializer := contract
  runtime := contract
}

private def templates : CheckedCreationTemplateRegistry := {
  lookup := fun selected => if selected = identifier then some template else none
}

private def calls : CheckedContractRegistry := {
  lookup := fun address => if address = targetAddress then some contract else none
}

private def templateLookupExact : Bool :=
  match templates.lookup identifier with
  | none => false
  | some selected =>
      selected.initializer.code.program == program &&
        selected.runtime.code.program == program &&
        (templates.lookup otherIdentifier).isNone

private def emptyAndCallsOnlyExact : Bool :=
  (CheckedCreationTemplateRegistry.empty.lookup identifier).isNone &&
    ((ExecutionEnvironment.callsOnly calls).creationTemplates.lookup
      identifier).isNone &&
    match (ExecutionEnvironment.callsOnly calls).callRegistry.lookup
        targetAddress with
    | none => false
    | some selected =>
        selected.code.program == program &&
          (ExecutionEnvironment.callsOnly calls).creationAddressPolicy.derive
            callerAddress identifier == ⟨0, by decide⟩

private theorem compileTimeEnvironmentExact :
    templateLookupExact && emptyAndCallsOnlyExact = true := by
  native_decide

def testAdr0148ExecutionEnvironment : IO Unit := do
  unless templateLookupExact do
    throw (IO.userError "checked creation template lookup changed")
  unless emptyAndCallsOnlyExact do
    throw (IO.userError "calls-only execution environment was not inert")

end Tests.Adr0148ExecutionEnvironment
