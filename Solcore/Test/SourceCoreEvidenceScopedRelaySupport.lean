import Solcore.Test.SourceCoreEvidenceScopedSyntax
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)

/-- Actual lexical and loop children share the selected Header's complete
ledger and dictionary, recovered separately at each reached source context. -/
theorem ActualHeader.scoped_support {fixture : CompiledFixture}
    {signature generic : ProgramFunctionSignature}
    {firstParameter secondParameter : TypeSystem.TypeParameterId}
    {firstType secondType : TypeSystem.Ty} {trait : ProgramTraitId}
    (row : ObservedRow fixture signature)
    (shape : RelayShape row.row.function signature generic firstParameter secondParameter firstType secondType trait)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (resultType : row.row.function.inferredBodyType = firstType)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (initial : Supported fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (loop : Supported fixture.recipe.compiled.indexed.base.plan shape.loopCall.instantiation)
    (final : Supported fixture.recipe.compiled.indexed.base.plan shape.finalCall.instantiation)
    (actual : ActualHeader fixture row.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) body
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have bodyEq : actual.header.function.body = shape.body := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = firstType := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact resultType
  have syntaxTree : GenericImperativeMatch.Syntax actual.header.function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.SupportedSyntax
        fixture.recipe.compiled.indexed.base.plan actual.header.function.source id)
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
    obtain ⟨facts, finalContext, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
    rw [actual.source, shape.roots, resultEq] at typed
    simp only [List.filterMap_cons, List.filterMap_nil] at typed
    rw [actual.source, bodyEq, resultEq]
    exact shape.body_syntax nodes (actual.source ▸ actual.header.unique) (shape.syntax initial loop final) typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    actual.aligned.accepted (by rw [actual.source, bodyEq]; exact shape.body_shape) actual.aligned.projection
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
    row := row.row, prepared := actual.prepared,
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row.row,
    aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .canonicalBranching receipt }
  refine ⟨body, ?_⟩
  apply CallableIndexedOwnedPreparedNamedEvidenceScopedCollectors.of_actual actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed (fun _ witness => witness)
    _ rows complete (bootstrap_zero fixture.recipe.compiled) entryMember receipt stagePrepared syntaxTree.prepared
  rw [actual.source]
  exact shape.metadata nodes actual.prepared.named noLocals

theorem ActualHeader.relayWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayWordRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) body
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_support observed.relayWordRow observed.relayWordShape observed.relayWordNodes
    observed.relayWordResultType observed.noLocals observed.relayWord_supported
    observed.relayWord_loop_supported observed.relayWord_final_supported rows complete
    observed.wordRow.entryMember receiver stagePrepared

theorem ActualHeader.relayBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayBoolRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support
        (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        registry actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) body
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_support observed.relayBoolRow observed.relayBoolShape observed.relayBoolNodes
    observed.relayBoolResultType observed.noLocals observed.relayBool_supported
    observed.relayBool_loop_supported observed.relayBool_final_supported rows complete
    observed.wordRow.entryMember receiver stagePrepared

end Tests.SourceCoreEvidenceScoped
