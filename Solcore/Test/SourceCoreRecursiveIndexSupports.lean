import Solcore.Test.SourceCoreRecursiveIndexProgramCertificate
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalProgramSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed completion) :
    headers support.rows = [support.makeHeader.header, support.echoHeader.header, support.chooseHeader.header, support.selectHeader.header] :=
  support.toOrdinaryInventory.header_list

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨inventory⟩ := ordinary_inventory fixture observed makeStages echoStages chooseStages selectStages
  obtain ⟨program⟩ := admission.certificate.issue_for_without_methods fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.makeRow.entryMember
    inventory.rows (admission.aligned inventory)
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.methods)
  exact ⟨{toOrdinaryInventory := inventory, program := program}⟩

end Tests.SourceCoreRecursiveIndex
