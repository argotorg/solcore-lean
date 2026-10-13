import Solcore.Test.SourceCoreCanonicalScopedMetadata
import Solcore.Test.SourceCoreCanonicalScopedTypes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

theorem ActualHeader.relay_body {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    actual.header.function.body = [observed.relayShape.initialized.id, observed.relayShape.statement.id] := by
  rw [actual.aligned.function]
  have accepted := actual.prepared.compilation.roots
  change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
  rw [actual.prepared.same, observed.relayShape.roots] at accepted
  exact (Except.ok.inj accepted).symm

theorem ActualHeader.relay_syntax {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    GenericImperativeMatch.Syntax actual.header.function.source (GeneralSyntax actual.header.function.source)
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
  obtain ⟨facts, final, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.relayShape.roots, actual.relay_result_type] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  rw [actual.source, actual.relay_body, actual.relay_result_type]
  exact observed.relay_body_syntax (actual.source ▸ actual.header.unique) observed.relay_initial_syntax
    (.leaf (.read observed.relayShape.finalRead.found observed.relayShape.finalRead.form)) typed

theorem ActualHeader.relay_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  apply CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted actual.aligned.accepted _ actual.aligned.projection
  rw [actual.source, actual.relay_body]
  exact observed.relay_body_shape

def ActualHeader.relay_bundle {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) :
    CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
  row := observed.relayRow.row, prepared := actual.prepared,
  instantiation := CallableNamedMetadata.instantiation observed.relayRow.row,
  aligned := actual.aligned, layouts := actual.aligned.layouts, compilation := .canonicalBranching receipt }

def ActualHeader.relay_support {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    (receipt : CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header)
    {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    CallableIndexedOwnedPreparedStagedCanonicalScopedStaticSupport.NamedSupport
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics) := by
  apply CallableIndexedOwnedPreparedNamedCanonicalScopedCollectors.of_actual actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed _ rows complete
    (bootstrap_zero fixture.recipe.compiled) observed.relayRow.entryMember receipt stagePrepared actual.relay_syntax
  rw [actual.source]
  exact .of_ordinary (observed.relay_metadata actual.prepared.named (by rw [actual.prepared.same]; exact observed.relayRow.assumptions))

end Tests.SourceCoreCanonicalScoped
