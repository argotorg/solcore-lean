import Solcore.Test.SourceCoreNestedFormationLambdaSites
import Solcore.Test.SourceCoreNestedFormationSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreNestedFormation
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

def ObservedProgram.family {fixture : CompiledFixture} (observed : ObservedProgram fixture)
    (identityHeader : ActualHeader fixture observed.identityRow.row)
    (makeHeader : ActualHeader fixture observed.makeRow.row)
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
      rcases observed.cached_source identityHeader makeHeader support.caller.selected with original | original
      · have found := code.sourceFound
        rw [support.source.trans original] at found
        exact False.elim (observed.identity_no_lambda _ _ (lookupExpression?_sound found) _ _ _ code.sourceForm)
      · exact support.source.trans original
    have found := code.sourceFound
    rw [sameSource] at found
    have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
        fixture.recipe.compiled.indexed support.caller.named function.source := by
      rw [sameSource]
      exact .of_ordinary (observed.make_metadata support.caller.named
        (observed.cached_assumptions identityHeader makeHeader support.caller.selected))
    obtain ⟨sidecar, _issued, selected⟩ :=
      CallableIndexedOwnedPreparedDirectStageScopeReceipts.code_scope code support.source_receipt support.body.unique
    have signatureMember : fixture.makeSignature ∈ fixture.recipe.compiled.sourceProgram.signatures.functions := by
      rw [fixture.sameProgram, fixture.signatures]; exact .tail _ (.head _)
    have sourceOwner : function.source.owner = fixture.makeSignature.id := by
      rw [sameSource]; exact observed.makeRow.sourceOwner
    rcases observed.make_lambda_shape found code.sourceForm with inner | outer
    · have bodyShape := inner.2.2
      have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
          function.source observed.makeShape.call.value.node.id function.body := by
        rw [bodyShape]
        exact .returning [] (by rw [sameSource]; exact observed.makeShape.innerReturnFound)
          observed.makeShape.innerReturnForm
      have tree : CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
          function.source observed.makeShape.call.value.node.id := by
        rw [sameSource]; exact observed.make_syntax
      obtain ⟨packet, canonical⟩ :=
        CallableIndexedOwnedPreparedStagedOrdinaryCanonicalTerminalSupport.of_actual
          stagePrepared code support provenance receiver fixture.source_wellFormed metadata rows complete
          signatureMember sourceOwner observed.makeShape.call.value.node.id terminal tree _ (.anonymous selected)
      exact ⟨⟨.canonicalTerminal packet, canonical⟩⟩
    · have resultType := outer.2.1
      have bodyShape := outer.2.2
      have original : support.caller.function.source = function.source :=
        support.caller.agreement.source.trans support.source.symm
      have graph : OccurrenceGraphWellFormed observed.makeRow.row.function.typedBody := by
        rw [← sameSource]; exact support.body.frame.code.graph
      have typed := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters
        support.body.frame support.body.extended
      obtain ⟨finalContext, facts, typed, _completes⟩ := typed
      have shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body := by
        rw [sameSource, bodyShape]; exact observed.outer_body_shape
      have tree : GenericImperativeMatch.Syntax function.source
          (CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport.Syntax support.caller)
          support.body.context (.statements true function.body) function.resultType := by
        rw [sameSource, bodyShape, resultType] at typed ⊢
        apply observed.outer_body_syntax (sameSource ▸ support.body.unique)
        · exact .general (by rw [original, sameSource]; exact observed.make_initial_syntax)
        · exact .formation (observed.inner_shape support.caller (original.trans sameSource) graph)
        · exact typed
      obtain ⟨packet, nested⟩ :=
        CallableIndexedOwnedPreparedStagedOrdinaryMixedScopedSupport.of_actual
          stagePrepared code support provenance prefixContext receiver fixture.source_wellFormed metadata
          rows complete signatureMember sourceOwner
          (bootstrap_zero fixture.recipe.compiled)
          observed.profile shape tree _ (.anonymous selected)
      exact ⟨⟨.nestedBranching packet, nested⟩⟩
  | principal owner captured code history support origin globals leading referenceIndex typed provenance =>
    exact False.elim (fixture.no_principal support.principal)

end Tests.SourceCoreNestedFormation
