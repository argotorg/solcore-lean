import Solcore.SourceSemantics.CoreLowering.CallableLocalReadSourceTransport
import Solcore.SourceSemantics.CoreLowering.CallableAppliedDynamicSourceMaterialization

/-! Local-reference metadata agrees with the independently substituted Source
carried by the same actual paired history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup
open Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
open CallableAncestryProfiles CallableBodyMetadataViews

/-- Each pair retains the successful preparation of that exact frame. -/
theorem authenticated
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    CallableAncestryPairedLookup.Authenticates inputs frame (some state) := by
  induction paired with
  | named selected => exact .named selected
  | lambda _prior allowed ih => exact .lambda ih allowed
  | applied _prior recipe _ih => exact recipe.authenticated

/-- The independent source of a real pair is exactly its original selected
caller under the source-active substitution recorded by that history. -/
theorem original_source
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      source = original.function.typedBody.applySubstitution state.metadata.active := by
  induction paired with
  | named selected =>
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    obtain ⟨metadata, metadataSelected, rfl⟩ := Option.map_eq_some_iff.mp selected
    obtain ⟨original, found, same, empty⟩ := CallableAncestryPairedProfiles.named_source inputs metadataSelected
    refine ⟨original, found, ?_⟩
    change metadata.source = original.function.typedBody.applySubstitution metadata.active
    rw [same, empty, EmptySourceSubstitution.source]
  | lambda _prior _allowed ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _prior recipe ih =>
    obtain ⟨original, found, same⟩ := ih
    obtain ⟨_row, _selected, _canonical, reachable⟩ :=
      CallableLocalReadSourceTransport.authenticated_original recipe.lexicalHistory
    refine ⟨original, found, ?_⟩
    change source.applySubstitution recipe.read.substitution =
      original.function.typedBody.applySubstitution (recipe.read.substitution.compose lexical.metadata.active)
    rw [same, SourceComposition.source recipe.read.substitution lexical.metadata.active
      (reachable.closed (CallableAncestrySourceActive.generators_valid inputs.views))]

/-- The actual runtime local read and the compiler metadata lookup are the
same complete record, including requirements and coercions. -/
theorem local_lookup
    {cached : SourceCoreUnifiedCompilation.Compiled} {inputs : Inputs cached.indexed.base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    {id : ExpressionId} {expression : ExpressionNode}
    (found : source.lookupExpression? id = some expression)
    {name : String} {localId : Resolved.LocalId}
    (form : expression.form = .reference name (.local localId)) :
    state.metadata.source.lookupExpression? id = some expression := by
  obtain ⟨original, selected, sourceEq⟩ := original_source paired
  rw [sourceEq, lookupExpression_apply] at found
  obtain ⟨raw, rawFound, same⟩ := Option.map_eq_some_iff.mp found
  have rawForm : raw.form = .reference name (.local localId) := by
    have substituted := congrArg ExpressionNode.form same
    rw [form] at substituted
    cases shape : raw.form <;> simp [ExpressionNode.applySubstitution, shape,
      ExpressionForm.applySubstitution] at substituted
    rename_i rawName resolution
    cases resolution <;> simp_all [ReferenceResolution.applySubstitution]
  have actual := CallableLocalReadSourceTransport.authenticated_local_lookup (authenticated paired) selected rawFound rawForm
  rw [same] at actual
  exact actual

/-- The same pair also retains the exact first-match local binder selector.
Erasure changes only expression requirement lists, which this selector ignores. -/
theorem binder_lookup
    {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame}
    {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source)
    (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? state.metadata.source id =
      SourceCompilationPlan.directLambdaLetBinder? source id := by
  rw [← CallableLocalReadSourceTransport.binder_erased state.metadata.source id,
    CallableAppliedDynamicSourceMaterialization.erase_source paired,
    CallableLocalReadSourceTransport.binder_erased source id]

end Solcore.SourceSemantics.CoreLowering.CallablePairedLocalReadLookup
