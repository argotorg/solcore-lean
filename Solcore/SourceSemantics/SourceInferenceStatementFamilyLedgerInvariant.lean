import Solcore.SourceSemantics.SourceInferenceForItemsLedgerInvariant
import Solcore.SourceSemantics.SourceInferenceMatchCasesLedgerInvariant

/-!
The statement-side family of pending-template ledger preservation theorems.
This groups the fuel-mutual statement, statement-list, for-header and match-arm
steps without depending on the expression-side implementation module.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.SourceInferenceSoundness

open Frontend Frontend.SourceInference TypeSystem

/-- All mutually dependent statement-side traversals at one fuel. -/
structure StatementFamilyLedgerPreservation (fuel : Nat) : Prop where
  statement : InferStatementFuelLedgerPreservation fuel
  statements : InferStatementsFuelLedgerPreservation fuel
  forItem : InferForItemFuelLedgerPreservation fuel
  forItems : InferForItemsFuelLedgerPreservation fuel
  matchCases : InferMatchCasesFuelLedgerPreservation fuel

/-- The whole statement-side family at fuel `n` depends only on expression,
place, assignment and pattern preservation at smaller fuel, plus the already
established statement-side family at smaller fuel.  The same-fuel `for` item
list is closed by structural list induction after its one-item theorem. -/
theorem statementFamilyLedgerPreservation_step
    {fuel : Nat}
    (exprPrev : ∀ childFuel, childFuel < fuel →
      InferExprFuelLedgerPreservation childFuel)
    (exprsPrev : ∀ childFuel, childFuel < fuel →
      InferExprsFuelLedgerPreservation childFuel)
    (placePrev : ∀ childFuel, childFuel < fuel →
      InferPlaceFuelLedgerPreservation childFuel)
    (assignedPrev : ∀ childFuel, childFuel < fuel →
      InferAssignedValueFuelLedgerPreservation childFuel)
    (patternPrev : ∀ childFuel, childFuel < fuel →
      ∀ {context : Frontend.SourceInference.Context}
        {pattern : Syntax.Pattern} {expected : Ty}
        {initial final : State} {inferred : TypedMatchPattern}
        {pending : List RequirementId},
        Detail.inferMatchPatternFuel childFuel context pattern expected
          initial = .ok (inferred, final) →
        RecursiveLedgerInvariant initial pending →
        RecursiveLedgerInvariant final pending)
    (familyPrev : ∀ childFuel, childFuel < fuel →
      StatementFamilyLedgerPreservation childFuel) :
    StatementFamilyLedgerPreservation fuel := by
  cases fuel with
  | zero =>
      have statementZero : InferStatementFuelLedgerPreservation 0 := by
        intro context statement expectedReturn initial result pending success
          tracked
        simp [Detail.inferStatementFuel] at success
      have statementsZero : InferStatementsFuelLedgerPreservation 0 := by
        intro context statements expectedReturn initial result pending success
          tracked
        simp [Detail.inferStatementsFuel] at success
      have forItemZero : InferForItemFuelLedgerPreservation 0 := by
        intro context item initial final inferred pending success tracked
        simp [Detail.inferForItemFuel] at success
      have casesZero : InferMatchCasesFuelLedgerPreservation 0 := by
        intro context scrutineeType expectedReturn outerScope cases initial
          result pending success tracked
        simp [Detail.inferMatchCasesFuel] at success
      exact ⟨statementZero, statementsZero, forItemZero,
        inferForItemsFuelLedgerPreservation_of_itemSoundness forItemZero,
        casesZero⟩
  | succ childFuel =>
      have previous := familyPrev childFuel (Nat.lt_succ_self childFuel)
      have itemCurrent : InferForItemFuelLedgerPreservation
          (childFuel + 1) :=
        inferForItemFuelLedgerPreservation_step
          (exprPrev childFuel (Nat.lt_succ_self childFuel))
          (placePrev childFuel (Nat.lt_succ_self childFuel))
          (assignedPrev childFuel (Nat.lt_succ_self childFuel))
      have itemsCurrent : InferForItemsFuelLedgerPreservation
          (childFuel + 1) :=
        inferForItemsFuelLedgerPreservation_of_itemSoundness itemCurrent
      have statementCurrent : InferStatementFuelLedgerPreservation
          (childFuel + 1) :=
        inferStatementFuelLedgerPreservation_step
          (exprPrev childFuel (Nat.lt_succ_self childFuel))
          (exprsPrev childFuel (Nat.lt_succ_self childFuel))
          previous.statements previous.forItems
          (placePrev childFuel (Nat.lt_succ_self childFuel))
          (assignedPrev childFuel (Nat.lt_succ_self childFuel))
          previous.matchCases
      have statementsCurrent : InferStatementsFuelLedgerPreservation
          (childFuel + 1) :=
        inferStatementsFuelLedgerPreservation_step
          (fun prior priorBound => (familyPrev prior priorBound).statement)
          (fun prior priorBound => (familyPrev prior priorBound).statements)
      have casesCurrent : InferMatchCasesFuelLedgerPreservation
          (childFuel + 1) :=
        inferMatchCasesFuelLedgerPreservation_step
          (patternPrev childFuel (Nat.lt_succ_self childFuel))
          previous.statements previous.matchCases
      exact ⟨statementCurrent, statementsCurrent, itemCurrent, itemsCurrent,
        casesCurrent⟩

end Solcore.SourceSemantics.SourceInferenceSoundness
