import Solcore.Test.SourceCoreCanonicalScopedMakeSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
    (relayHeader : ActualHeader fixture observed.relayRow.row)
    (extra : ObservedMake fixture observed)
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
    have bodyShape := (observed.make_lambda_shape found code.sourceForm).2.2
    have resultShape := (observed.make_lambda_shape found code.sourceForm).2.1
    have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
      rw [sameSource, bodyShape]; exact observed.make_body_shape
    obtain ⟨_final, _facts, bodyTyped, _completes⟩ := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
      support.body.frame support.body.extended
    have tree : GenericImperativeMatch.Syntax function.source
        (CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax function.source)
        support.body.context (.statements true function.body) function.resultType := by
      rw [sameSource, bodyShape, resultShape] at bodyTyped ⊢
      exact observed.make_body_syntax extra.binderScheme (sameSource ▸ support.body.unique) observed.make_children bodyTyped
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader relayHeader support.caller.selected))
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    exact
      CallableIndexedOwnedPreparedStagedOrdinaryCanonicalScopedSupport.of_actual
        stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
        (signature := fixture.makeSignature)
        (by rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.tail _ (.head _)))
        (by rw [sameSource]; exact observed.makeRow.sourceOwner)
        shape tree _ (.anonymous selected)
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreCanonicalScoped
