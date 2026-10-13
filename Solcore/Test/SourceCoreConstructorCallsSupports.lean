import Solcore.Test.SourceCoreConstructorCallsProgramCertificate
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed makeStages readStages
  obtain ⟨program⟩ := admission.certificate.issue_for_without_methods fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    inventory.rows (admission.aligned inventory)
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)
  exact ⟨{toOrdinaryInventory := inventory, program := program}⟩

end Tests.SourceCoreConstructorCalls
