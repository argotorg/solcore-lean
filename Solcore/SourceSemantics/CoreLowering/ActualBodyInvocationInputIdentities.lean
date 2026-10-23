import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles

/-! Input identities come from the actual named seed and compiler plan row.
Arbitrary later substitutions preserve them, including a larger read context.
No equality of input types or of complete source tables is needed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes

private theorem inputs_substitution (source : TypedSource) (substitution : Substitution) :
    (source.applySubstitution substitution).inputs.map TypedBinder.id =
      source.inputs.map TypedBinder.id := by
  simp only [TypedSource.applySubstitution, List.map_map, Function.comp_def, TypedBinder.applySubstitution]

theorem paired_input_origin {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : SourceCoreCallablePairedFrames.Frame} {state : SourceCoreCallableAncestryReadRecipes.State} {source : TypedSource}
    (paired : CallableAppliedDynamicSourceMaterialization.Pair inputs frame state source) :
    ∃ original, SourceCompilationPlan.exactSpecialization base.plan state.metadata.owner = .ok original ∧
      source.inputs.map TypedBinder.id = original.function.typedBody.inputs.map TypedBinder.id := by
  induction paired with
  | @named id state selected =>
    unfold SourceCoreCallableAncestryPairedPreparation.named? at selected
    cases found : SourceCoreCallableAncestryPreparation.named? inputs id with
    | none => simp [found] at selected
    | some metadata =>
      simp only [found, Option.map_some, Option.some.injEq] at selected
      subst state
      obtain ⟨original, selected, source, _⟩ :=
        CallableAncestryPairedProfiles.named_source inputs found
      exact ⟨original, selected, congrArg (fun source : TypedSource =>
        source.inputs.map TypedBinder.id) source⟩
  | lambda _ _ ih => exact ih
  | @applied callerFrame lexicalFrame caller lexical source id target _ recipe ih =>
    obtain ⟨original, selected, same⟩ := ih
    exact ⟨original, selected, (inputs_substitution source recipe.read.substitution).trans same⟩

private theorem compiler_input_origin {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {owner : SourceCompilationPlan.Key} {active : Substitution} {source : TypedSource}
    (receipt : LambdaSourceAlignment.SourceReceipt program plan owner active source) :
    ∃ original, SourceCompilationPlan.exactSpecialization plan owner = .ok original ∧
      source.inputs.map TypedBinder.id = original.function.typedBody.inputs.map TypedBinder.id := by
  cases receipt with
  | original selected => exact ⟨_, selected, rfl⟩
  | contextual accepted =>
    obtain ⟨original, selected, _, _, source⟩ := LambdaSourceAlignment.prepared_source accepted
    exact ⟨original, selected, by rw [source]; exact inputs_substitution _ _⟩

/-- Both paths select the same actual plan row. This works for every carried
paired source, independently of the view relation chosen for its code. -/
theorem Index.input_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) :
    index.source.inputs.map TypedBinder.id = index.compilerSource.inputs.map TypedBinder.id := by
  cases index with
  | named _ _ => rfl
  | contextual material view =>
    obtain ⟨original, selected, source⟩ := paired_input_origin view.materialized_pair
    obtain ⟨compiler, compiled, target⟩ := compiler_input_origin material.compiler_source_receipt
    have owner := view_metadata_owner view
    rw [owner] at selected
    have same := Except.ok.inj (selected.symm.trans compiled)
    subst compiler
    exact source.trans target.symm

theorem Index.compiler_source_receipt {compiled : SourceCoreUnifiedCompilation.Compiled}
    {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) :
    LambdaSourceAlignment.SourceReceipt compiled.indexed.base.sourceProgram compiled.indexed.base.plan
      index.owner index.active index.compilerSource := by
  cases index with
  | named _ selected => exact .original selected
  | contextual material _ => exact material.compiler_source_receipt

theorem materialized_input_ids {compiled : SourceCoreUnifiedCompilation.Compiled}
    {mapping : GeneralHeap.LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {viewRelation : TypedSource → TypedSource → Prop}
    (material : GeneralizedLocalAcceptedMaterialization.Materialization compiled mapping world function viewRelation)
    (view : GeneralizedLocalAcceptedMaterialization.View material) :
    function.source.inputs.map TypedBinder.id = material.code.view.inputs.map TypedBinder.id :=
  (Index.contextual (bodyRelation := fun source target _ => viewRelation source target) material view).input_ids

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
