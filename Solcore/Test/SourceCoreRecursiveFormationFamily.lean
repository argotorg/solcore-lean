import Solcore.Test.SourceCoreRecursiveFormationMakeSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows))
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {registry : SourceCoreRawMetadata.Registry}
    {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result) :
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association := by
  cases association with
  | ordinary owner captured code history support origin prefixContext globals referenceIndex typed provenance =>
    apply CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor.compiled
    have sameSource : function.source = observed.makeRow.row.function.typedBody := by
      rcases observed.cached_source identityHeader makeHeader relayHeader support.caller.selected with original | original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.relay_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
    have found := code.sourceFound
    rw [sameSource] at found
    obtain ⟨shape, _member, _parameters, _result, bodyShape⟩ := observed.make_lambda_shape found code.sourceForm
    have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
        function.source shape.call.value.node.id function.body := by
      rw [bodyShape]
      exact .returning [] (by rw [sameSource]; exact shape.innerReturnFound)
        shape.innerReturnForm
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader relayHeader support.caller.selected))
    have tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        function.source shape.call.value.node.id := by
      rw [sameSource]; exact shape.syntax
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    obtain ⟨packet, canonical⟩ :=
      CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport.of_actual
        stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
        (signature := fixture.makeSignature)
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        (by rw [sameSource]; exact observed.makeRow.sourceOwner)
        shape.call.value.node.id terminal tree _ (.anonymous selected)
    exact ⟨⟨.canonicalTerminal packet, canonical⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreRecursiveFormation
