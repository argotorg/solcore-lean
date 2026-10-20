import Solcore.SourceSemantics.SourceCompiledProvenanceExpressionContracts
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceInferenceGeneralizedExpressionListState
import Solcore.SourceSemantics.SourceInferenceSelectedBuiltinCall

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem builtinCall_typing_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsHere : callProvenance (.expressions childFuel inferenceContext argumentSources initial arguments argumentState))
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (recording : Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  let roots := bodyRoots selected
  let evidenceState := selected.body.returned
  have resources := selected.body.resources
  have interfaces := boundary.interfaces
  have resultSubstitutionExtension := boundary.extension
  have ownerEq := boundary.scope.owner
  have typeParametersEq := boundary.scope.parameters
  have signatureFormation := boundary.scope.formation checked
  have functionsCanonical := boundary.scope.functionsCanonical checked
  have canonical := boundary.scope.canonical checked
  have actual := boundary.actual
  have semanticPreserved := boundary.proper
  have rawProper := boundary.rawProper
  have integerPatternsSubset := boundary.integerPatterns
  have integerLiteralsSubset := boundary.integerLiterals
  have requirementsSubset := boundary.requirements
  have covered := boundary.covered
  have actualCovered := boundary.actualCovered
  have argumentProperties := Detail.inferExprsFuel_inferenceProperties invariant.ready
    signatureFormation functionsCanonical argumentsSuccess
  have expectedAtArguments : ∀ type ∈ expected, type.VariablesBelow argumentState.inference.next :=
    fun type member => (expectedBelow type member).weaken argumentProperties.1.next_le
  have recordProperties := Detail.recordBuiltinFunctionCall_inferenceProperties
    argumentProperties.2.1 argumentProperties.2.2 expectedAtArguments recording
  have argumentExtension := resultSubstitutionExtension.trans recordProperties.1.substitution_extends
  have metadata := recordBuiltinFunctionCall_metadata recording
  obtain ⟨calleeId, nodesEq⟩ := Detail.recordBuiltinFunctionCall_success_nodes recording
  have argumentToParent : TypingSourceExtends (argumentState.toTypedSource roots)
      (resultState.toTypedSource roots) := by
    refine ⟨metadata.1, ?_⟩
    change argumentState.nodes <+: resultState.nodes
    rw [nodesEq]
    exact List.prefix_append _ _
  let callNode : ExpressionNode := {
    id := inferred.id
    span := expression.span
    type := inferred.type
    form := .call calleeId (arguments.map (·.id)) (.builtinFunction function)
  }
  have callContains : ContainsExpression (resultState.toTypedSource roots) inferred.id callNode := by
    refine ⟨?_, rfl⟩
    change .expression callNode ∈ resultState.nodes
    rw [nodesEq]
    simp [callNode]
  have argumentEdge : ∀ argument ∈ arguments,
      DirectChild (resultState.toTypedSource roots) (.expression inferred.id) (.expression argument.id) := by
    intro argument member
    refine ⟨.expression callNode, ⟨callContains.1, rfl⟩, ?_⟩
    simp only [callNode, nodeChildIds, Node.references, ExpressionForm.references, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨argument.id, List.mem_map.mpr ⟨argument, member, rfl⟩, rfl⟩)
  have argumentPatterns : argumentState.integerPatterns ⊆ evidenceState.integerPatterns := by
    rw [← metadata.2.1]
    exact integerPatternsSubset
  have argumentLiterals : argumentState.integerLiterals ⊆ evidenceState.integerLiterals := by
    rw [← metadata.2.2]
    exact integerLiteralsSubset
  have argumentRequirements := List.Subset.trans
    (Detail.recordBuiltinFunctionCall_requirements_subset recording) requirementsSubset
  have argumentsTyped := expressionsRooted_for checked descend childFuel recursive
    argumentsHere argumentsSuccess interfaces argumentExtension boundary.scope invariant actual operational
    (fun argument member => (rawProper.childSubtree (argumentEdge argument member)).monoBefore argumentToParent)
    argumentPatterns argumentLiterals argumentRequirements
    (fun argument member => covered.expressionChild resources.graph_closed (boundary.directChildren (argumentEdge argument member)))
    (fun argument member => actualCovered.directChild (boundary.directChildren (argumentEdge argument member)))
  exact recordBuiltinFunctionCall_expressionTypingBase_actual recording resultSubstitutionExtension
    semanticPreserved argumentsTyped
    (invariant.typeParameterBinders (by simpa only [ownerEq, typeParametersEq] using canonical))


theorem builtinCall_typing
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel parentFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {expected : Option Ty} {parentInitial initial argumentState resultState : State}
    {inferred : InferredExpression} {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    {argumentSources : List Syntax.Expr} {arguments : List InferredExpression}
    {name : String} {function : BuiltinFunctionId} {call : ExpressionId}
    (boundary : RetainedExpressionBoundary selected parentFuel inferenceContext expression expected
      parentInitial inferred resultState frames target)
    (invariant : RecursiveExpressionInvariant (checkingContext selected) selected.body.finalized initial target)
    (operational : GeneralizedActualStateInvariant initial (evidenceSource selected))
    (expectedBelow : ∀ type ∈ expected, type.VariablesBelow initial.inference.next)
    (argumentsSuccess : Detail.inferExprsFuel childFuel inferenceContext argumentSources initial =
      .ok (arguments, argumentState))
    (recording : Detail.recordBuiltinFunctionCall expression callee name function arguments
      call expected argumentState = .ok (inferred, resultState)) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred := by
  exact builtinCall_typing_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    boundary invariant operational expectedBelow True.intro argumentsSuccess recording

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
