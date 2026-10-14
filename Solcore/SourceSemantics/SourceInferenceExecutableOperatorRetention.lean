import Solcore.SourceSemantics.SourceInferenceExecutableCoercionRetention

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open ExecutableCoercionInterfaces

/-- Later coercion attachment preserves the original operator dispatch and
its complete ordinary requirement prefix at the same source identity. -/
def ExpressionOperatorSiteRetainedAt
    (before after : TypedSource) (id : ExpressionId) : Prop :=
  ∀ {node}, ContainsExpression before id node →
    ∀ primary companions name,
      node.requirements = (primary :: companions) ++ node.coercions.flatMap CoercionStep.requirements →
      operatorDispatch node name →
      ∃ finalNode, ContainsExpression after id finalNode ∧
        finalNode.requirements = (primary :: companions) ++ finalNode.coercions.flatMap CoercionStep.requirements ∧
        operatorDispatch finalNode name

namespace ExpressionOperatorSiteRetainedAt

theorem refl (source : TypedSource) (id : ExpressionId) :
    ExpressionOperatorSiteRetainedAt source source id := by
  intro node found primary companions name layout dispatch
  exact ⟨node, found, layout, dispatch⟩

theorem trans {before middle after : TypedSource} {id : ExpressionId}
    (first : ExpressionOperatorSiteRetainedAt before middle id)
    (second : ExpressionOperatorSiteRetainedAt middle after id) :
    ExpressionOperatorSiteRetainedAt before after id := by
  intro node found primary companions name layout dispatch
  obtain ⟨middleNode, middleFound, middleLayout, middleDispatch⟩ :=
    first found primary companions name layout dispatch
  exact second middleFound primary companions name middleLayout middleDispatch

theorem monoBefore {before middle after : TypedSource} {id : ExpressionId}
    (extension : TypingSourceExtends before middle)
    (retained : ExpressionOperatorSiteRetainedAt middle after id) :
    ExpressionOperatorSiteRetainedAt before after id := by
  intro node found
  exact retained (extension.containsExpression found)

private theorem dispatch_substitution (substitution : Substitution) (node : ExpressionNode)
    (name : String) : operatorDispatch (node.applySubstitution substitution) name =
      operatorDispatch node name := by
  cases form : node.form <;>
    simp [operatorDispatch, ExpressionNode.applySubstitution, ExpressionForm.applySubstitution, form]

private theorem coercion_ids_substitution (substitution : Substitution) (steps : List CoercionStep) :
    (steps.map (CoercionStep.applySubstitution substitution)).flatMap CoercionStep.requirements =
      steps.flatMap CoercionStep.requirements := by
  induction steps with
  | nil => rfl
  | cons step rest ih => simp [CoercionStep.applySubstitution, CoercionStep.requirements, ih]

theorem ofExpressionNodesPreservedAt {before after : TypedSource} {id : ExpressionId}
    (substitution : Substitution)
    (preserved : ExpressionNodesPreservedAt [id]
      (before.applySubstitution substitution) after) :
    ExpressionOperatorSiteRetainedAt before after id := by
  intro node found primary companions name layout dispatch
  refine ⟨node.applySubstitution substitution,
    preserved (by simp) (FlexibleSubstitution.ContainsExpression.applySubstitution substitution found), ?_, ?_⟩
  · simpa only [ExpressionNode.applySubstitution, coercion_ids_substitution] using layout
  · simpa only [dispatch_substitution] using dispatch

theorem ofTypingSourceExtends {before after : TypedSource} {id : ExpressionId}
    (substitution : Substitution)
    (extension : TypingSourceExtends (before.applySubstitution substitution) after) :
    ExpressionOperatorSiteRetainedAt before after id :=
  ofExpressionNodesPreservedAt substitution
    (ExpressionNodesPreservedAt.ofTypingSourceExtends extension)

theorem ofAttachExpressionCoercions
    {state : State} {entries : List Detail.ExpressionCoercions}
    {entry : Detail.ExpressionCoercions} {roots : List NodeId}
    (unique : (entries.map (·.expression)).Nodup) (member : entry ∈ entries) :
    ExpressionOperatorSiteRetainedAt (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) entry.expression := by
  intro node found primary companions name layout dispatch
  refine ⟨Detail.appendExpressionCoercions node entry.coercions,
    attachExpressionCoercions_containsExpression state entries entry node roots unique member found, ?_, ?_⟩
  · simp only [Detail.appendExpressionCoercions, layout, Detail.coercionRequirements, List.flatMap_append, List.append_assoc]
  · exact dispatch

theorem traitName {signatures : ProgramSignatures} {requirements : List SolvedRequirement}
    {before after : TypedSource} {id : ExpressionId}
    (retained : ExpressionOperatorSiteRetainedAt before after id)
    (interfaces : SourceInterfaces signatures requirements after)
    {node : ExpressionNode} (found : ContainsExpression before id node)
    {primary : RequirementId} {companions : List RequirementId} {name : String}
    (layout : node.requirements = (primary :: companions) ++ node.coercions.flatMap CoercionStep.requirements)
    (dispatch : operatorDispatch node name)
    {solved : SolvedRequirement} (member : solved ∈ requirements)
    (identity : solved.id = primary)
    {trait : Resolved.DeclarationId} (selected : solved.predicate.trait = .declaration trait) :
    (signatures.trait? trait).map (·.name) = some name := by
  obtain ⟨finalNode, finalFound, finalLayout, finalDispatch⟩ :=
    retained found primary companions name layout dispatch
  obtain ⟨actual, actualTrait, unique, actualSelected, actualName⟩ :=
    interfaces.operators finalNode finalFound.1 primary companions name finalLayout finalDispatch
  have present : solved ∈ requirements.filter (fun row => decide (row.id = primary)) :=
    List.mem_filter.mpr ⟨member, by simp only [identity, decide_true]⟩
  rw [unique] at present
  have same : solved = actual := List.mem_singleton.mp present
  subst actual
  have sameTrait : trait = actualTrait := by simpa only [selected, ProgramTraitId.declaration.injEq] using actualSelected
  simpa only [sameTrait] using actualName

end ExpressionOperatorSiteRetainedAt
end Solcore.SourceSemantics.SourceInferenceSoundness
