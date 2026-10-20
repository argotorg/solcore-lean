import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}

theorem RootedExpressionBoundary.finalSubtree
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    SubtreePreserved selected.body.finalized.substitution
      (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      (.expression inferred.id) := by
  rw [selected.body.resources.source_eq]
  exact boundary.rawSubtree.substituted _

theorem RootedExpressionBoundary.finalNodes
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    ExpressionNodesPreservedAt [inferred.id]
      ((resultState.toTypedSource (bodyRoots selected)).applySubstitution selected.body.finalized.substitution)
      selected.body.finalized.typedSource := by
  intro id node member contains
  have same : id = inferred.id := by simpa using member
  subst id
  exact boundary.finalSubtree.subgraph.containsExpression contains (.inl rfl)

theorem RootedExpressionBoundary.retained
    (boundary : RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target) :
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target := by
  refine { boundary.toExpressionCallBoundary with
    proper := boundary.finalSubtree.proper
    rawProper := boundary.rawSubtree.proper
    expressionRequirements := ?_
    coercionPrimaries := ExpressionCoercionPrimariesRetainedAt.ofExpressionNodesPreservedAt _ boundary.finalNodes
    operatorSite := ExpressionOperatorSiteRetainedAt.ofExpressionNodesPreservedAt _ boundary.finalNodes
    directChildren := ExpressionDirectChildrenRetainedAt.ofExpressionNodesPreservedAt boundary.finalNodes }
  intro node requirement contains member
  have found := boundary.finalNodes (by simp)
    (FlexibleSubstitution.ContainsExpression.applySubstitution _ contains)
  apply found.primaryRequirementOccursAt
  simpa [ExpressionNode.applySubstitution] using member

/-- Root preservation upgrades retained expression typing using the same
selected finalizer's formation proof for that actual recorded node. -/
theorem expressionRooted_of_retained {raw : Workspace.RawWorkspace}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRootedSoundness selected childFuel := by
  intro inferenceContext expression expected initial resultState inferred frames target boundary
  have base := sound boundary.retained
  cases base with
  | @intro node rawType plan contains typeEq formType rawAdmissible requirements =>
      have member : Node.expression node ∈ (evidenceSource selected).nodes :=
        boundary.rawSubtree.nodes (.expression node) contains.1
          (.inl (congrArg NodeId.expression contains.2))
      have canonical := boundary.scope.canonical checked
      have finalAdmissible : TypeAdmissible target
          (selected.body.finalized.substitution.apply inferred.type) := by
        have formed := selected.body.resources.expressionTypeAdmissible_in_active member
          (boundary.invariant.typeParameterBinders (by
            simpa [boundary.scope.owner, boundary.scope.parameters] using canonical))
          boundary.invariant.signatures_eq_whole boundary.invariant.typeParametersEq
          boundary.invariant.declarationEq boundary.invariant.residual
        simpa only [typeEq] using formed
      exact (ExpressionTypingBase.intro contains typeEq formType rawAdmissible requirements
        ).expressionHasType boundary.finalNodes finalAdmissible

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
