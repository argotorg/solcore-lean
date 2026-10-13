import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority

/-! A retained method dictionary is accepted only when the actual method
materializer and the method caller's resolver produce the same complete list.
The validator preserves order, repeated goals and every nested evidence tree.
It is a static check and contains no Source or native execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
open Frontend SourceInference
open CallableNamedMetadata (environment evidence evidence_represents)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (ResolvedCaller)

abbrev Dictionary := SourceTypedRuntime.RuntimeEvidenceEnvironment

/-- Actual accepted compiler materialization, together with the exact resolver
result required when that selected method becomes a caller. -/
structure Materialized (program : CheckedProgram)
    (caller : SourceSpecialization.SpecializedFunction) (node : ExpressionNode)
    (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) where
  dictionary : Dictionary
  materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
    .ok dictionary
  resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program
    selection.method.specialized.key selection.method.specialized.assumptions = .ok dictionary

/-- The check compares complete raw dictionaries, not merely their goals or
runtime projections. Rejection means this static producer is unavailable. -/
def validate (program : CheckedProgram) (caller : SourceSpecialization.SpecializedFunction)
    (node : ExpressionNode) (selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod) :
    Option (Materialized program caller node selection) :=
  match materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection with
  | .error _ => none
  | .ok dictionary =>
      match resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program
          selection.method.specialized.key selection.method.specialized.assumptions with
      | .error _ => none
      | .ok actual =>
          if same : actual = dictionary then
            some ⟨dictionary, materialized, same ▸ resolved⟩
          else none

variable {program : CheckedProgram} {caller : SourceSpecialization.SpecializedFunction}
  {node : ExpressionNode} {selection : SourceCompilationPlan.CheckedRuntimeOperatorMethod}

/-- Matching the compiler's own accepted action transfers the receipt to its
exact retained dictionary. No equality supplied by a public caller is used. -/
def Materialized.for_actual (receipt : Materialized program caller node selection)
    {dictionary : Dictionary}
    (accepted : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
      .ok dictionary) :
    ResolvedCaller program selection.method.specialized (environment dictionary) := by
  have same : receipt.dictionary = dictionary := Except.ok.inj (receipt.materialized.symm.trans accepted)
  exact ⟨dictionary, same ▸ receipt.resolved, rfl⟩

/-- A successful per-position resolver spine reconstructs the genuine whole
resolver action at any specialization key. -/
theorem resolve_of_resolved {goals : List ProgramPredicate} {dictionary : Dictionary}
    (resolved : CallableCoercionEvidenceOrigins.Resolved program goals dictionary)
    (key : SourceCompilationPlan.Key) :
    SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key goals = .ok dictionary := by
  induction resolved with
  | nil => rfl
  | @cons goal raw goals rest head tail ih =>
      obtain ⟨semantic, represented, valid⟩ := TraitResolutionSoundness.resolve_success_evidenceValid head
      have same := represented.functional (evidence_represents raw)
      rw [same] at valid
      have goalEq : SourceCompilationPlan.runtimeEvidenceGoal raw = goal := by
        simpa only [CallableEvidenceEnvironment.evidence_goal] using valid.evidence_goal_eq
      cases raw with
      | byImpl actual implementation premises =>
          simp only [SourceCompilationPlan.resolveRuntimeEvidenceEnvironment, head]
          change actual = goal at goalEq
          simp [goalEq, ih]
          rfl

/-- Structural static proofs of every retained tree can construct the same
receipt without invoking the executable validator. -/
def of_resolved {dictionary : Dictionary}
    (materialized : SourceCompilationPlan.operatorMethodRuntimeEvidence program caller node selection =
      .ok dictionary)
    (resolved : CallableCoercionEvidenceOrigins.Resolved program selection.method.specialized.assumptions dictionary) :
    Materialized program caller node selection :=
  ⟨dictionary, materialized, resolve_of_resolved resolved selection.method.specialized.key⟩

end Solcore.SourceSemantics.CoreLowering.CallableMethodResolverEvidence
