import Solcore.Test.SourceCoreCapturedLocalMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSingleReadSequence

/-! Every authentic returned closure of this compiled program receives the
body-reached single-read certificate. The initializer read elsewhere in the
same source remains distinct and contributes only its own original metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

def ActualHeader.closure_family {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row)
    {headers : List (CallableIndexedOwnedFunctionValues.Header fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key fixture.recipe.compiled
      (Program.ofChecked fixture.recipe.compiled.sourceProgram))}
    {registry : SourceCoreRawMetadata.Registry}
    {completion : SourceCoreCallableIndexedPrograms.Completion fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor
      (actualStagePrepared fixture) association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.sequence
    have sameSource := support.source.trans (stages.source_of_cached actual support.caller.selected)
    have found := code.sourceFound
    rw [sameSource] at found
    have bodyShape := (observed.lambda_shape found code.sourceForm).2.2
    exact CallableIndexedOwnedPreparedStagedSingleReadSequence.sequence_on (actualStagePrepared fixture)
      code support provenance receiver fixture.source_wellFormed
      (by rw [sameSource]; exact observed.metadata support.caller.named)
      bodyShape (by rw [sameSource]; exact observed.foundInnerReturn) observed.innerReturnForm
      (by rw [sameSource]; exact observed.foundRead) observed.readForm
      observed.readRequirements observed.readCoercions observed.noLocals
      fixture.signature fixture.signature_member (by rw [sameSource]; exact observed.sourceOwner)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCapturedLocal
