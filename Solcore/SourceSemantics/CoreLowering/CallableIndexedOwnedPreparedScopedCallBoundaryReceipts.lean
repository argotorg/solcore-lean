import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualDiagnosticSources
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualCalleeStageReceipts

/-! A genuine contextual Source view preserves the original indirect call's
callee and ordered argument identities. The original node and metadata remain
attached to the original selected codebook row; substituted metadata are kept
separately. The static boundary factory uses the same actual Prepared site,
caller and table. These receipts concern static source and artifact provenance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)

/-- The actual node is either the original node or its actual substitution.
This retains the embedded argument types and coercion metadata explicitly. -/
def CallView (before actual : ExpressionNode)
    (originalMetadata metadata : IndirectCallResolution) : Prop :=
  (actual = before ∧ metadata = originalMetadata) ∨
    ∃ active, actual = before.applySubstitution active ∧
      metadata = originalMetadata.applySubstitution active

/-- Type substitution leaves the physical argument count unchanged. -/
theorem CallView.argument_count {before actual : ExpressionNode}
    {originalMetadata metadata : IndirectCallResolution}
    (view : CallView before actual originalMetadata metadata) :
    metadata.argumentCount = originalMetadata.argumentCount := by
  rcases view with ⟨_, same⟩ | ⟨active, _, same⟩
  · rw [same]
  · rw [same]; rfl

/-- Recover the original indirect metadata from an actual substituted form.
The callee and ordered IDs remain literal; embedded types are not equated. -/
theorem substituted_indirect_origin (active : TypeSystem.Substitution)
    (node : ExpressionNode) {callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution}
    (form : (node.applySubstitution active).form = .call callee ids (.indirect metadata)) :
    ∃ originalMetadata, node.form = .call callee ids (.indirect originalMetadata) ∧
      metadata = originalMetadata.applySubstitution active := by
  cases originalForm : node.form <;>
    simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, originalForm] at form <;>
    try cases form
  case call actualCallee actualIds resolution =>
    cases resolution with
    | indirect originalMetadata =>
        simp only [CallResolution.applySubstitution] at form
        obtain ⟨sameCallee, sameIds, sameMetadata⟩ := ExpressionForm.call.inj form
        cases sameCallee
        cases sameIds
        exact ⟨originalMetadata, rfl, (CallResolution.indirect.inj sameMetadata).symm⟩
    | declaration instantiation => cases form
    | builtinFunction function => cases form

/-- One actual contextual Source occurrence recovers its original call node
and retains the exact forward relation between both metadata records. -/
theorem indirect_origin {original actual : TypedSource}
    (view : SourceView original actual) {id : ExpressionId} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    (contains : ContainsExpression actual id node)
    (form : node.form = .call callee ids (.indirect metadata)) :
    ∃ before originalMetadata, ContainsExpression original id before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before node originalMetadata metadata := by
  rcases view with same | ⟨active, same⟩
  · subst actual
    exact ⟨node, metadata, contains, form, .inl ⟨rfl, rfl⟩⟩
  · subst actual
    obtain ⟨before, retained, sameNode⟩ :=
      CallableIndexedOwnedContextualDiagnosticSources.substituted_contains contains
    subst node
    obtain ⟨originalMetadata, originalForm, sameMetadata⟩ :=
      substituted_indirect_origin active before form
    exact ⟨before, originalMetadata, retained, originalForm,
      .inr ⟨active, rfl, sameMetadata⟩⟩

section Caller
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {sidecar : SourceCoreStageContracts.Sidecar}

include compiler prepared in
/-- The existing finite static factory runs at the actual original call node.
Its selected row is tied to this original metadata and the same native site. -/
theorem boundary_at_original {before : ExpressionNode} {originalMetadata : IndirectCallResolution}
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (contains : ContainsExpression sidecar.source prepared.site.call before)
    (form : before.form = .call callee ids (.indirect originalMetadata))
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  have stages := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  have atSite := stages.accepted
  rw [← prepared.table] at atSite
  have rows := CallCodebookCertificates.rows_of_prepareWithProjection atSite caller contains form
  have origin : CallableLedger.OriginRep sidecar.plan prepared.site.table sourceValue carrier := by
    have plan := (CallContractCertificates.sidecar_of_accepted caller).1
    rw [plan, prepared.table]
    exact actualOrigin
  cases origin with
  | @closure function raw entry owner occurrence active contract member entryOrigin retained provenance =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.closure member entryOrigin retained provenance) provenance.binds
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique dispatch.found
      exact .user dispatch selected
  | @named function raw entry key contract member entryOrigin retained target contractPrepared =>
      obtain ⟨dispatch⟩ := CallableLedger.dispatch rows
        (CallableLedger.OriginRep.named member entryOrigin retained target contractPrepared)
        (CallableLedger.Binds.named target contractPrepared)
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique dispatch.found
      exact .user dispatch selected
  | @builtin function raw entry member entryOrigin retained =>
      obtain ⟨ledger⟩ := rows entry member
      have selected := CallableIndexedOwnedSelectedCallCodebookReceipts.selected_at_prepared stages
        prepared.table caller contains form unique ledger.found
      refine .builtin ⟨selected, ?_, ?_, ?_, ledger.builtin retained⟩
      · rw [ledger.entry_eq]; exact entryOrigin
      · rw [ledger.entry_eq]; exact retained
      · refine ⟨raw, ?_⟩
        rw [ledger.entry_eq]

include compiler prepared in
/-- The actual compiler occurrence and authentic Source view supply the
original static factory. No equality between the whole Sources is required. -/
theorem boundary_at_source_view
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
    (view : SourceView sidecar.source source)
    (unique : NodeOccurrencesUnique sidecar.source)
    {sourceValue : Dynamic.Value} {carrier : Value}
    (actualOrigin : CallableLedger.OriginRep compiled.indexed.base.plan
      compiled.indexed.ancestry.graph.inputs.callable.table sourceValue carrier) :
    ∃ before originalMetadata, ContainsExpression sidecar.source prepared.site.call before ∧
      before.form = .call callee ids (.indirect originalMetadata) ∧
      CallView before compiler.original originalMetadata metadata ∧
      BoundaryAt sidecar prepared.site callee ids originalMetadata before sourceValue carrier := by
  have actualContains : ContainsExpression source prepared.site.call compiler.original := by
    rw [prepared.call]
    exact lookupExpression?_sound compiler.found
  obtain ⟨before, originalMetadata, contains, form, callView⟩ :=
    indirect_origin view actualContains compiler.originalForm
  exact ⟨before, originalMetadata, contains, form, callView,
    boundary_at_original compiler prepared caller contains form unique actualOrigin⟩

end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedScopedCallBoundaryReceipts
