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
open SourceCompiledLocalFinalization

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
  generalize allocation : initial.allocateExpressionId = allocatedPair
  obtain ⟨id, allocated⟩ := allocatedPair
  have invariant := boundary.invariant.allocateExpressionId allocation
  have operational := boundary.operational.allocateExpressionId
  rw [allocation] at operational
  have expectedBelow : ∀ type ∈ expected, type.VariablesBelow allocated.inference.next := by
    rw [allocateExpressionId_inferenceNext_eq allocation]
    exact boundary.expectedBelow
  cases inferExprFuel_success_call_dispatch_facts form allocation boundary.accepted with
  | constructor discovery fresh application =>
    exact constructor_call checked (recursive childFuel (Nat.lt_succ_self _)) form
      (by simpa only [allocation] using discovery) boundary
  | selected argumentsSuccess origin selection recording =>
    exact selectedCall_typing checked
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentsSuccess selection recording origin.candidatesSubset
  | builtin argumentsSuccess recording =>
    exact builtinCall_typing checked
      (fun smaller less => recursive smaller (Nat.lt_trans less (Nat.lt_succ_self _)))
      boundary invariant operational expectedBelow argumentsSuccess recording
  | indirect argumentsSuccess calleeSuccess applicationSuccess recording =>
    exact indirectCall_typing checked recursive boundary invariant operational expectedBelow
      argumentsSuccess calleeSuccess applicationSuccess recording

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
