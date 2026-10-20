import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.SourceCompiledGeneralizedExpressionRooted

/-! The original semantic boundaries are reused with a separate predicate on
the exact inference call. Actual execution provenance can restrict recursion;
the existing unrestricted APIs use the constantly true predicate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization SourceInferenceExecution

variable {compiled : SourceCoreCompiler.Compiled}
    {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

def ExpressionRetainedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.expression childFuel inferenceContext expression expected initial inferred resultState) →
    RetainedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionTypingBase (resultState.toTypedSource (bodyRoots selected))
      selected.body.finalized.typedSource target selected.body.finalized.substitution inferred

def ExpressionRootedSoundnessFor (provenance : CallIndex → Prop)
    (selected : BodySelection compiled row fuel) (childFuel : Nat) : Prop :=
  ∀ {inferenceContext : SourceInference.Context} {expression : Syntax.Expr} {expected : Option Ty}
    {initial resultState : State} {inferred : InferredExpression}
    {frames : List InitializedLetBinding} {target : SourceSemantics.Context},
    provenance (.expression childFuel inferenceContext expression expected initial inferred resultState) →
    RootedExpressionBoundary selected childFuel inferenceContext expression expected
      initial inferred resultState frames target →
    ExpressionHasType selected.body.finalized.typedSource target inferred.id
      (selected.body.finalized.substitution.apply inferred.type)

/-- An unrestricted proof can be used at any retained call predicate. -/
theorem expressionRetainedSoundnessFor_restrict
    {provenance : CallIndex → Prop}
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRetainedSoundnessFor provenance selected childFuel :=
  fun _ boundary => sound boundary

theorem expressionRetainedSoundnessFor_true
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundness selected childFuel) :
    ExpressionRetainedSoundnessFor (fun _ => True) selected childFuel :=
  fun _ boundary => sound boundary

theorem expressionRetainedSoundness_of_true
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (sound : ExpressionRetainedSoundnessFor (fun _ => True) selected childFuel) :
    ExpressionRetainedSoundness selected childFuel :=
  fun boundary => sound trivial boundary

/-- Both provenance modes share the same final-node formation proof. -/
theorem expressionRooted_of_retained_for {raw : Workspace.RawWorkspace}
    {provenance : CallIndex → Prop}
    {selected : BodySelection compiled row fuel} {childFuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    (sound : ExpressionRetainedSoundnessFor provenance selected childFuel) :
    ExpressionRootedSoundnessFor provenance selected childFuel := by
  intro inferenceContext expression expected initial resultState inferred frames target here boundary
  exact boundary.typing_of_base checked (sound here boundary.retained)

end Solcore.SourceSemantics.SourceCompiledGeneralizedSoundness
