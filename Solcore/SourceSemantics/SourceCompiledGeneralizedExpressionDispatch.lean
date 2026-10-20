import Solcore.SourceSemantics.SourceCompiledBodySelectionFormation
import Solcore.SourceSemantics.SourceCompiledGeneralizedAtomicSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedGroupSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedTupleSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedConditionalSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedBinarySoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedIndexSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedCallSoundness
import Solcore.SourceSemantics.SourceCompiledGeneralizedLambdaSoundness

/-! Expression dispatch uses smaller actual expression calls and the statement
family at the lambda body's fuel. Lambda entry supplies the concrete return
privacy and admissibility conditions from its actual parameter prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel childFuel : Nat}
    {selected : BodySelection compiled row fuel}

def StatementsRootedSoundness (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {statements : List Syntax.Statement}
    {expectedReturn : Ty} {initial : State} {result : Detail.BlockResult}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    (∀ binder ∈ initial.localBinders,
      ProtectedVariables.Safe binder.scheme.quantified initial expectedReturn) →
    TypeAdmissible target (selected.body.finalized.substitution.apply expectedReturn) →
    StatementsBoundary selected childFuel inferenceContext statements expectedReturn
      initial result frames target →
    StatementsConclusion selected inferenceContext expectedReturn result frames target

theorem expressionRetained_zero : ExpressionRetainedSoundness selected 0 := by
  intro inferenceContext expression expected initial resultState inferred frames target boundary
  have success := boundary.accepted
  simp only [Detail.inferExprFuel] at success
  cases success

theorem expressionRetained_step_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel) :
    ExpressionRetainedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro inferenceContext expression expected initial resultState inferred frames target here boundary
  have predecessor : ExpressionRetainedSoundnessFor callProvenance selected childFuel :=
    recursive childFuel (Nat.lt_succ_self childFuel)
  cases form : expression.value with
  | literal literal =>
      exact expressionRetained_literal checked form boundary
  | identifier name =>
      exact expressionRetained_identifier checked form boundary
  | proxy marker type =>
      exact expressionRetained_proxy checked form boundary
  | group inner =>
      exact expressionRetained_group_for checked descend predecessor here form boundary
  | tuple elements =>
      exact expressionRetained_tuple_for checked descend recursive here form boundary
  | unary operator operand =>
      exact expressionRetained_unary_for checked descend recursive here form boundary
  | binary left operator right =>
      exact expressionRetained_binary_for checked descend predecessor here form boundary
  | conditional condition question thenBranch colon elseBranch =>
      exact expressionRetained_conditional_for checked descend predecessor here form boundary
  | index base brackets index =>
      exact expressionRetained_index_for checked descend predecessor here form boundary
  | lambda keyword parameters returnAnnotation body =>
      exact expressionRetained_lambda_for checked descend here form boundary
        (fun bodyHere safe admissible bodyBoundary => bodySound bodyHere safe admissible bodyBoundary)
  | call callee arguments =>
      exact expressionRetained_call_for checked descend recursive here form boundary
  | dotConstructor dot name arguments =>
      exact constructor_dot_for checked descend predecessor here form boundary
  | field base dot name =>
      exact constructor_field_for checked descend predecessor here form boundary
  | array elements =>
      have success := boundary.accepted
      simp only [Detail.inferExprFuel, form] at success
      cases success
  | error =>
      have success := boundary.accepted
      simp only [Detail.inferExprFuel, form] at success
      cases success

theorem expressionRetained_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (bodySound : StatementsRootedSoundness selected childFuel) :
    ExpressionRetainedSoundness selected (childFuel + 1) := by
  exact expressionRetained_step_for (callProvenance := fun _ => True) checked true_childClosed
    (fun smaller less => by
      intro context source expected initial final value frames target _ boundary
      exact recursive smaller less boundary)
    (fun _ safe admissible boundary => bodySound safe admissible boundary) True.intro

theorem expressionRooted_zero
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ExpressionRootedSoundness selected 0 :=
  expressionRooted_of_retained checked expressionRetained_zero

theorem expressionRooted_step
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundness selected smaller)
    (bodySound : StatementsRootedSoundness selected childFuel) :
    ExpressionRootedSoundness selected (childFuel + 1) :=
  expressionRooted_of_retained checked (expressionRetained_step checked recursive bodySound)


theorem expressionRetained_zero_for {callProvenance : CallIndex → Prop} :
    ExpressionRetainedSoundnessFor callProvenance selected 0 := by
  intro context source expected initial final value frames target _ boundary
  exact expressionRetained_zero boundary

theorem expressionRooted_zero_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program) :
    ExpressionRootedSoundnessFor callProvenance selected 0 := by
  intro context source expected initial final value frames target here boundary
  exact expressionRooted_of_retained_for checked expressionRetained_zero_for here boundary

theorem expressionRooted_step_for {callProvenance : CallIndex → Prop}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (descend : ChildClosed callProvenance)
    (recursive : ∀ smaller, smaller < childFuel + 1 → ExpressionRetainedSoundnessFor callProvenance selected smaller)
    (bodySound : StatementsRootedSoundnessFor callProvenance selected childFuel) :
    ExpressionRootedSoundnessFor callProvenance selected (childFuel + 1) := by
  intro context source expected initial final value frames target here boundary
  exact expressionRooted_of_retained_for checked
    (expressionRetained_step_for checked descend recursive bodySound) here boundary

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
