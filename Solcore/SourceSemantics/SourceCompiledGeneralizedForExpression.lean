import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledProvenanceStatementContracts

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem forItem_expression_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ExpressionRootedSoundnessFor callProvenance selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expression : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.forItem (childFuel + 1) inferenceContext item initial inferred final))
    (form : item.value = .expression expression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  obtain ⟨value, resultState, child, resultEq⟩ :=
    inferForItemFuel_success_expression_facts form boundary.accepted
  have sameItem : inferred = .expression value.id := congrArg Prod.fst resultEq
  have sameState : final = resultState := congrArg Prod.snd resultEq
  subst inferred
  subst final
  have member : (.expression value.id : NodeId) ∈ (ForItemForm.expression value.id).references := by
    simp [ForItemForm.references]
  have childHere := descend here (.forItem_expression boundary.accepted form child)
  have typed := recursive childHere ({
    accepted := child
    interfaces := boundary.interfaces
    extension := boundary.extension
    scope := boundary.scope
    invariant := RecursiveExpressionInvariant.ofStatement boundary.invariant
    actual := boundary.actual
    operational := boundary.operational
    expectedBelow := by simp
    expectedAdmissible := by simp
    expectedSafe := by simp
    rawSubtree := boundary.rawReferences _ member
    integerPatterns := boundary.integerPatterns
    integerLiterals := boundary.integerLiterals
    requirements := boundary.requirements
    covered := boundary.covered _ member
    actualCovered := boundary.actualCovered _ member
  } : RootedExpressionBoundary selected childFuel inferenceContext expression none
    initial value resultState frames target)
  exact ⟨target, boundary.invariant.inferExprFuel child (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) (by simp) boundary.extension,
    boundary.actual, boundary.operational.ofExpression boundary.invariant.ready
      (boundary.scope.catalog checked) (boundary.scope.formation checked)
      (boundary.scope.functionsCanonical checked) (by simp) (by simp) child,
    ForItemHasType.expression typed⟩

theorem forItem_expression
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ExpressionRootedSoundness selected childFuel)
    {inferenceContext : SourceInference.Context} {item : Syntax.ForItem} {expression : Syntax.Expr}
    {expectedReturn : Ty} {initial final : State} {inferred : ForItemForm}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : item.value = .expression expression)
    (boundary : ForItemBoundary selected (childFuel + 1) inferenceContext item expectedReturn
      initial inferred final frames target) :
    ForItemConclusion selected inferenceContext expectedReturn inferred final frames target := by
  exact forItem_expression_for (callProvenance := fun _ => True) checked true_childClosed
    (fun _ boundary => recursive boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
