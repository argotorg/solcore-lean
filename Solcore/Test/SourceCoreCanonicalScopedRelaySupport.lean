import Solcore.Test.SourceCoreCanonicalScopedTypes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
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

theorem ActualHeader.relay_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  exact CallableIndexedOwnedPreparedNamedEvidenceAdmission.receipt
    actual.prepared actual.aligned observed.relayAdmission.selected observed.relayAdmission.same
    observed.relayAdmission.certificate

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
  exact CallableIndexedOwnedPreparedNamedEvidenceAdmission.of_receipt
    actual.prepared actual.aligned observed.relayAdmission.selected observed.relayAdmission.same
    observed.relayAdmission.certificate rows complete fixture.recipePrepared actual.diagnostic
    receiver fixture.source_wellFormed (bootstrap_zero fixture.recipe.compiled)
    observed.relayRow.entryMember receipt stagePrepared

end Tests.SourceCoreCanonicalScoped
