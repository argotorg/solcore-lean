import Solcore.SourceSemantics.SourceInferenceExpressionCallProvenance
import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedNamedCall
import Solcore.SourceSemantics.SourceCompiledGeneralizedBuiltinCall
import Solcore.SourceSemantics.SourceCompiledGeneralizedIndirectCall
import Solcore.SourceSemantics.SourceCompiledGeneralizedConstructorSoundness

/-! Actual call dispatch selects constructor, named, builtin or indirect
execution. Every branch consumes the same selected body's child hypotheses. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

theorem expressionRetained_call_for {callProvenance : CallIndex → Prop}
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (here : callProvenance (.expression (childFuel + 1) inferenceContext expression expected initial inferred resultState))
    (form : expression.value = .call callee arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  cases inferExprFuel_success_call_dispatch_provenance_facts form allocation boundary.accepted with
  | constructor discovery fresh application =>
    exact constructor_call_for checked descend (recursive childFuel (Nat.lt_succ_self _)) here form
      (by simpa only [allocation] using discovery) boundary
  | selected nonconstructor argumentsSuccess origin selection recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    have argumentCalls := OrderedExpressionCalls.of_call descend argumentsHere argumentsSuccess
    exact selectedCall_typing_for checked
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentCalls argumentsSuccess selection recording origin.candidatesSubset
  | builtin nonconstructor argumentsSuccess recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    exact builtinCall_typing_for checked descend
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentsHere argumentsSuccess recording
  | indirect nonconstructor argumentsSuccess indirect calleeSuccess applicationSuccess recording =>
    have argumentsHere := descend here (.expression_call_arguments boundary.accepted form allocation nonconstructor argumentsSuccess)
    have calleeHere := descend here (.expression_call_callee boundary.accepted form allocation nonconstructor argumentsSuccess indirect calleeSuccess)
    exact indirectCall_typing_for checked descend recursive boundary invariant operational expectedBelow
      argumentsHere argumentsSuccess calleeHere calleeSuccess applicationSuccess recording

theorem expressionRetained_call
    {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    {inferenceContext : SourceInference.Context} {expression callee : Syntax.Expr}
    {arguments : Syntax.DelimitedList Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context}
    (form : expression.value = .call callee arguments)
    (boundary : RetainedExpressionBoundary selected (childFuel + 1) inferenceContext expression
      expected initial inferred resultState frames target) :
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected)) selected.body.finalized.typedSource
      target selected.body.finalized.substitution inferred := by
  exact expressionRetained_call_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary) True.intro form boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
