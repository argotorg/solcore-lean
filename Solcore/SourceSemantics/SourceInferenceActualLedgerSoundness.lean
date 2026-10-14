import Solcore.SourceSemantics.SourceInferenceActualExpressionLedger
import Solcore.SourceSemantics.SourceInferenceActualPatternLedger
import Solcore.SourceSemantics.SourceInferenceStatementFamilyLedgerInvariant
import Solcore.SourceSemantics.SourceInferencePlaceLedgerInvariant

/-! The operational ledger family is independent of declarative typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend Frontend.SourceInference TypeSystem

structure ActualLedgerFamily (fuel : Nat) : Prop where
  expression : InferExprFuelLedgerPreservation fuel
  expressions : InferExprsFuelLedgerPreservation fuel
  place : InferPlaceFuelLedgerPreservation fuel
  assigned : InferAssignedValueFuelLedgerPreservation fuel
  statements : StatementFamilyLedgerPreservation fuel

theorem actualLedgerFamily_of_patternPreservation
    (patterns : ∀ fuel, ∀ {context : Frontend.SourceInference.Context}
      {pattern : Syntax.Pattern} {expected : Ty}
      {initial final : State} {inferred : TypedMatchPattern}
      {pending : List RequirementId},
      Detail.inferMatchPatternFuel fuel context pattern expected initial = .ok (inferred, final) →
      RecursiveLedgerInvariant initial pending → RecursiveLedgerInvariant final pending) :
    ∀ fuel, ActualLedgerFamily fuel := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | ind fuel previous =>
      have expression : InferExprFuelLedgerPreservation fuel := by
        cases fuel with
        | zero =>
            intro context expression expected initial final inferred pending success _
            simp [Detail.inferExprFuel] at success
        | succ child =>
            have prior := previous child (Nat.lt_succ_self child)
            intro context expression expected initial final inferred pending accepted tracked
            exact inferExprFuelLedgerPreservation_step prior.expression prior.expressions prior.statements.statements
              accepted tracked
      have expressions : InferExprsFuelLedgerPreservation fuel :=
        inferExprsFuelLedgerPreservation_step
          (fun child bound => (previous child bound).expression)
          (fun child bound => (previous child bound).expressions)
      have place : InferPlaceFuelLedgerPreservation fuel :=
        inferPlaceFuel_ledgerPreservation fuel
          (fun child bound => (previous child bound).expression)
      have assigned : InferAssignedValueFuelLedgerPreservation fuel :=
        inferAssignedValueFuel_ledgerPreservation place expression
      have statements : StatementFamilyLedgerPreservation fuel :=
        statementFamilyLedgerPreservation_step
          (fun child bound => (previous child bound).expression)
          (fun child bound => (previous child bound).expressions)
          (fun child bound => (previous child bound).place)
          (fun child bound => (previous child bound).assigned)
          (fun child _ => patterns child)
          (fun child bound => (previous child bound).statements)
      exact ⟨expression, expressions, place, assigned, statements⟩

/-- The entire executable inference family preserves its actual ledger state.
The statement family includes local declarations, loop headers and match arms. -/
theorem actualLedgerFamily : ∀ fuel, ActualLedgerFamily fuel := by
  apply actualLedgerFamily_of_patternPreservation
  intro fuel context pattern expected initial final inferred pending accepted tracked
  exact inferMatchPatternFuel_ledgerPreservation accepted tracked

end Solcore.SourceSemantics.SourceInferenceSoundness
