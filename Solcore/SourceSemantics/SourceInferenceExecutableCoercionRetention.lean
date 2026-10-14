import Solcore.SourceSemantics.SourceExecutableCoercionInterfaces
import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness

/-! A retained expression root may acquire more output coercions when its
enclosing call is resolved. Each earlier coercion primary still belongs to a
real final coercion site, which supplies its executable method interface. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem
open ExecutableCoercionInterfaces

def CoercionPrimariesPresent (source : TypedSource) (steps : List CoercionStep) : Prop :=
  ∀ step ∈ steps, ∃ node, .expression node ∈ source.nodes ∧
    ∃ finalStep ∈ node.coercions ++ indirectArgumentCoercions node,
      finalStep.requirement = step.requirement

def ExpressionCoercionPrimariesRetainedAt
    (before after : TypedSource) (id : ExpressionId) : Prop :=
  ∀ {node}, ContainsExpression before id node →
    ∀ step ∈ node.coercions ++ indirectArgumentCoercions node,
      ∃ finalNode, ContainsExpression after id finalNode ∧
        ∃ finalStep ∈ finalNode.coercions ++ indirectArgumentCoercions finalNode,
          finalStep.requirement = step.requirement

theorem indirectArgumentCoercions_applySubstitution
    (substitution : Substitution) (node : ExpressionNode) :
    indirectArgumentCoercions (node.applySubstitution substitution) =
      (indirectArgumentCoercions node).map (CoercionStep.applySubstitution substitution) := by
  cases form : node.form <;>
    simp only [ExpressionNode.applySubstitution, ExpressionForm.applySubstitution,
      form, indirectArgumentCoercions, List.map_nil]
  case call callee arguments resolution =>
    cases resolution <;> rfl

namespace ExpressionCoercionPrimariesRetainedAt

theorem present {before after : TypedSource} {id : ExpressionId}
    (retained : ExpressionCoercionPrimariesRetainedAt before after id)
    {node : ExpressionNode} (found : ContainsExpression before id node) :
    CoercionPrimariesPresent after (node.coercions ++ indirectArgumentCoercions node) := by
  intro step site
  obtain ⟨finalNode, finalFound, finalStep, finalSite, identity⟩ := retained found step site
  exact ⟨finalNode, finalFound.1, finalStep, finalSite, identity⟩

theorem refl (source : TypedSource) (id : ExpressionId) :
    ExpressionCoercionPrimariesRetainedAt source source id := by
  intro node found step member
  exact ⟨node, found, step, member, rfl⟩

theorem trans {before middle after : TypedSource} {id : ExpressionId}
    (first : ExpressionCoercionPrimariesRetainedAt before middle id)
    (second : ExpressionCoercionPrimariesRetainedAt middle after id) :
    ExpressionCoercionPrimariesRetainedAt before after id := by
  intro node found step member
  obtain ⟨middleNode, middleFound, middleStep, middleMember, middleId⟩ := first found step member
  obtain ⟨finalNode, finalFound, finalStep, finalMember, finalId⟩ := second middleFound middleStep middleMember
  exact ⟨finalNode, finalFound, finalStep, finalMember, finalId.trans middleId⟩

theorem monoBefore {before middle after : TypedSource} {id : ExpressionId}
    (extension : TypingSourceExtends before middle)
    (retained : ExpressionCoercionPrimariesRetainedAt middle after id) :
    ExpressionCoercionPrimariesRetainedAt before after id := by
  intro node found
  exact retained (extension.containsExpression found)

theorem ofExpressionNodesPreservedAt {before after : TypedSource} {id : ExpressionId}
    (substitution : Substitution)
    (preserved : ExpressionNodesPreservedAt [id]
      (before.applySubstitution substitution) after) :
    ExpressionCoercionPrimariesRetainedAt before after id := by
  intro node found step member
  refine ⟨node.applySubstitution substitution,
    preserved (by simp) (FlexibleSubstitution.ContainsExpression.applySubstitution substitution found),
    step.applySubstitution substitution, ?_, rfl⟩
  rw [indirectArgumentCoercions_applySubstitution]
  change step.applySubstitution substitution ∈
    node.coercions.map (CoercionStep.applySubstitution substitution) ++ _
  rw [← List.map_append]
  exact List.mem_map.mpr ⟨step, member, rfl⟩

theorem ofTypingSourceExtends {before after : TypedSource} {id : ExpressionId}
    (substitution : Substitution)
    (extension : TypingSourceExtends (before.applySubstitution substitution) after) :
    ExpressionCoercionPrimariesRetainedAt before after id :=
  ofExpressionNodesPreservedAt substitution
    (ExpressionNodesPreservedAt.ofTypingSourceExtends extension)

theorem ofAttachExpressionCoercions
    {state : State} {entries : List Detail.ExpressionCoercions}
    {entry : Detail.ExpressionCoercions} {roots : List NodeId}
    (unique : (entries.map (·.expression)).Nodup) (member : entry ∈ entries) :
    ExpressionCoercionPrimariesRetainedAt (state.toTypedSource roots)
      ((Detail.attachExpressionCoercions state entries).toTypedSource roots) entry.expression := by
  intro node found step site
  refine ⟨Detail.appendExpressionCoercions node entry.coercions,
    attachExpressionCoercions_containsExpression state entries entry node roots unique member found,
    step, ?_, rfl⟩
  rcases List.mem_append.mp site with output | argument
  · exact List.mem_append_left _ (List.mem_append_left _ output)
  · exact List.mem_append_right _ argument

theorem profile_at {signatures : ProgramSignatures} {requirements : List SolvedRequirement}
    {before after : TypedSource} {id : ExpressionId}
    (retained : ExpressionCoercionPrimariesRetainedAt before after id)
    (interfaces : SourceInterfaces signatures requirements after)
    {node : ExpressionNode} (found : ContainsExpression before id node)
    {step : CoercionStep} (site : step ∈ node.coercions ++ indirectArgumentCoercions node)
    {solved : SolvedRequirement} (solvedMember : solved ∈ requirements)
    (sameRequirement : solved.id = step.requirement)
    {trait : Resolved.DeclarationId} (traitEq : solved.predicate.trait = .declaration trait)
    {context : Frontend.SourceInference.Context} (same : context.signatures = signatures) :
    ∃ profile : Detail.CoercionMethodProfile,
      Detail.coercionMethodProfile? context trait = .ok (some profile) := by
  obtain ⟨finalNode, finalFound, finalStep, finalSite, identity⟩ := retained found step site
  exact interfaces.profile_at finalFound.1 finalSite solvedMember
    (sameRequirement.trans identity.symm) traitEq same

theorem interface_at {signatures : ProgramSignatures} {requirements : List SolvedRequirement}
    {before after : TypedSource} {id : ExpressionId}
    (retained : ExpressionCoercionPrimariesRetainedAt before after id)
    (interfaces : SourceInterfaces signatures requirements after)
    {node : ExpressionNode} (found : ContainsExpression before id node)
    {step : CoercionStep} (site : step ∈ node.coercions ++ indirectArgumentCoercions node)
    {solved : SolvedRequirement} (solvedMember : solved ∈ requirements)
    (sameRequirement : solved.id = step.requirement) :
    HasInterface signatures solved.predicate.trait := by
  obtain ⟨finalNode, finalFound, finalStep, finalSite, identity⟩ := retained found step site
  exact interfaces.interface_at finalFound.1 finalSite solvedMember
    (sameRequirement.trans identity.symm)

end ExpressionCoercionPrimariesRetainedAt
end Solcore.SourceSemantics.SourceInferenceSoundness
