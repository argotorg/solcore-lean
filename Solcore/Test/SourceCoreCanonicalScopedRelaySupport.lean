import Solcore.Test.SourceCoreCanonicalScopedCompilerExpressions
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyExpressionAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedEvidenceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodies
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCanonicalScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)

/-- Both the statement tree and its ordered expression actions come from the
actual accepted compiler body. The original finite metadata remains explicit. -/
theorem ActualHeader.relay_admission {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedNamedScopedAdmission.Admission actual.prepared actual.header
      observed.relayAdmission.table.rows := by
  rcases AcceptedNamedBodyExpressionAdmission.of_actual actual.prepared actual.aligned
      actual.relay_metadata observed.relay_direct_supported actual.relay_direct_sites
      fixture.source_wellFormed with admission | unsupported
  · exact admission
  · obtain ⟨unsupported⟩ := unsupported
    cases unsupported with
    | «structure» receipt outside =>
        rw [(actual.relay_compiler_details receipt).1] at outside
        cases outside
    | generalized receipt binding member quantified =>
        have present := List.mem_map.mpr
          (show ∃ selected ∈ receipt.tree.bindings, selected.binder = binding.binder from ⟨binding, member, rfl⟩)
        rw [(actual.relay_compiler_details receipt).2.1] at present
        have same := List.mem_singleton.mp present
        exact False.elim (quantified (by rw [same, observed.relayShape.localScheme]; rfl))
    | expression receipt child member residual =>
        have present := List.mem_map.mpr
          (show ∃ selected ∈ receipt.tree.children, selected.expression = child.expression from ⟨child, member, rfl⟩)
        rw [(actual.relay_compiler_details receipt).2.2] at present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        have reached : RelayReached observed child.expression := by
          rcases present with initial | final
          · exact .inl initial
          · exact .inr (.inr final)
        exact False.elim (actual.relay_expression_residual_impossible reached residual)

/-- This is the same evidence certificate consumed by the existing public
family. Its Source admission is derived from the compiler action. -/
def ActualHeader.relay_certificate {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    CallableIndexedOwnedPreparedNamedEvidenceAdmission.Certificate fixture.recipe.compiled observed.relayAdmission.named := {
  table := observed.relayAdmission.table
  sourceAdmission := AcceptedNamedBodyAdmission.source_of_header actual.prepared actual.aligned
    observed.relayAdmission.selected observed.relayAdmission.same actual.relay_admission
  requirements := observed.relayAdmission.requirements }

theorem ActualHeader.relay_receipt {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.relayRow.row) :
    Nonempty (CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.Receipt actual.header) := by
  exact CallableIndexedOwnedPreparedNamedEvidenceAdmission.receipt
    actual.prepared actual.aligned observed.relayAdmission.selected observed.relayAdmission.same
    actual.relay_certificate

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
    actual.relay_certificate rows complete fixture.recipePrepared actual.diagnostic
    receiver fixture.source_wellFormed (bootstrap_zero fixture.recipe.compiled)
    observed.relayRow.entryMember receipt stagePrepared

end Tests.SourceCoreCanonicalScoped
