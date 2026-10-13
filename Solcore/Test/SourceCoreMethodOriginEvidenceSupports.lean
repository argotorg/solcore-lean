import Solcore.Test.SourceCoreMethodOriginEvidenceProgramCertificate
import Solcore.Test.SourceCoreMethodOriginEvidenceSelection

/-! The single actual program certificate supplies named, closure and method
support together. The fixture retains only its original public header order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, makeWordInput, makeBoolInput, relayWordInput, relayBoolInput, useWordInput, useBoolInput, identityWordInput, identityBoolInput].map (fun input => input.prepared.index)).Nodup
  program : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support fixture.recipe.compiled
    (headers toOrdinaryInventory.rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
    completion

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (admission : ObservedProgramCertificate fixture observed) (receiver : ObservedReceiver fixture observed) :
    Nonempty (StaticSupportPackage fixture observed receiver.completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨program⟩ := admission.certificate.issue_for_checked fixture.source_wellFormed
    fixture.recipePrepared receiver.issued receiver.registry observed.wordRow.entryMember
    given.rows (admission.aligned given) (by rw [fixture.sameProgram]; exact fixture.checked)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := given.distinct
    program := program }⟩

end Tests.SourceCoreMethodOriginEvidence
