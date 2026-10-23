import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadTransport
import Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup

/-! The actual paired caller supplies the metadata lookup and original ledger
needed by prepareRead. Qualified factories come from executable preparation,
including every helper added to its completed frontier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedQualifiedReadFactory
open Frontend SourceInference TypeSystem
open CallableBodyMetadataViews
open SourcePreparedQualifiedLocalReadWitnesses SourcePreparedQualifiedLocalReadTransport

private theorem exact_member {plan : SourceSpecializationWorklist.Plan}
    {key : SourceSpecialization.SpecializationKey} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted <;> try contradiction
  cases accepted
  rename_i selected
  have present : row ∈ plan.specializations.filter (fun item => decide (item.key = key)) := by
    rw [selected]
    exact List.mem_singleton_self _
  exact (List.mem_filter.mp present).1

/-- The cache's successful complete preparation retains witnesses for every
row, including rows absent from the caller's initial validation plan. -/
theorem cached_covered (cached : SourceCoreUnifiedCompilation.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (member : caller ∈ cached.indexed.base.plan.specializations) :
    Covered cached.sourceProgram caller := by
  have prepared := SourceCoreUnifiedPreparationCertificates.compiled_planPrepared cached
  unfold SourceCompilationPlan.prepareExecutablePlanEvidence at prepared
  exact prepared_selected prepared member

/-- A real runtime local read has a successful metadata witness factory on the
same original specialization. No read-factory success, rewritten-source equality,
or source/native substitution equality is required from the consumer. -/
theorem paired_factory
    {cached : SourceCoreUnifiedCompilation.Compiled}
    {inputs : SourceCoreCallableAncestryPreparation.Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    {id : ExpressionId} {expression : ExpressionNode}
    (found : source.lookupExpression? id = some expression)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId))
    {binder : TypedBinder}
    (detected : SourceCompilationPlan.directLambdaLetBinder? source localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) :
    ∃ original available owned substitution witnesses,
      SourceCompilationPlan.exactSpecialization cached.indexed.base.plan state.metadata.owner = .ok original ∧
      SourceCompilationPlan.resolveRuntimeEvidenceEnvironment cached.indexed.base.sourceProgram
        original.key original.assumptions = .ok available ∧
      state.metadata.source.lookupExpression? id = some expression ∧
      SourceCompilationPlan.directLambdaLetBinder? state.metadata.source localId = some binder ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? expression = some owned ∧
      SourceCompilationPlan.localRequirementWitnesses original available binder
        {expression with type := expression.rawType, requirements := owned, coercions := []} =
          .ok (substitution, witnesses) := by
  obtain ⟨original, selected, sourceEq⟩ := CallablePairedLocalReadLookup.original_source paired
  have actualLookup := CallablePairedLocalReadLookup.local_lookup paired found form
  have actualBinder := (CallablePairedLocalReadLookup.binder_lookup paired localId).trans detected
  rw [sourceEq, lookupExpression_apply] at found
  obtain ⟨node, nodeFound, nodeEq⟩ := Option.map_eq_some_iff.mp found
  have rawForm : node.form = .reference name (.local localId) := by
    have substituted := congrArg ExpressionNode.form nodeEq
    rw [form] at substituted
    cases shape : node.form <;> simp [ExpressionNode.applySubstitution, shape,
      ExpressionForm.applySubstitution] at substituted
    rename_i rawName resolution
    cases resolution <;> simp_all [ReferenceResolution.applySubstitution]
  rw [sourceEq, CallableLocalReadSourceTransport.binder_apply] at detected
  obtain ⟨originalBinder, originalDetected, binderEq⟩ := Option.map_eq_some_iff.mp detected
  have originalQualified : originalBinder.schemeRequirements ≠ [] := by
    intro empty
    apply qualified
    rw [← binderEq]
    simp only [TypedBinder.applySubstitution, empty, List.map_nil]
  have member := exact_member selected
  obtain ⟨index, named, position, namedEq⟩ := SelectedCompilationCachedSources.row_position cached member
  have metadata := SourceCachedTemplateReceipts.cached_metadata cached position
  rw [namedEq] at metadata
  obtain ⟨available, owned, substitution, witnesses, resolved, ordinary, _binderFixed, _typeFixed, factory⟩ :=
    raw_of_preparation (cached_covered cached member) metadata
      (lookupExpression?_sound nodeFound).1 rawForm originalDetected originalQualified state.metadata.active
  have program := (SourceCoreUnifiedPreparationCertificates.compiled_fields cached).1
  rw [← program] at resolved
  rw [nodeEq] at ordinary factory
  rw [binderEq] at factory
  exact ⟨original, available, owned, substitution, witnesses, selected, resolved,
    actualLookup, actualBinder, ordinary, factory⟩

end Solcore.SourceSemantics.CoreLowering.CallablePairedQualifiedReadFactory
