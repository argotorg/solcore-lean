import Solcore.Syntax.Parser.PredicateSequenceTailProperties

/-! Contracts for grouped and comma-separated predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PredicateInternals

/-- Bare predicate sequences retain every predicate and their outer range. -/
theorem barePredicates_validFor :
    barePredicates.ValidFor
      (NonemptyDelimitedList.ValidFor Predicate.ValidFor) := by
  intro input inputValid
  unfold barePredicates
  cases firstResult : predicate input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := predicate_validFor input inputValid
      rw [firstResult] at valid
      exact valid
  | ok first next =>
      have firstValid := predicate_validFor input inputValid
      rw [firstResult] at firstValid
      rcases predicate_startsAtCurrentTokenOnSuccess input first next
          firstResult with ⟨anchor, anchorFound, anchorStart⟩
      have anchorFoundNext :
          next.tokens[input.cursor]? = some anchor := by
        rw [predicate_preservesTokensOnSuccess input first next firstResult]
        exact State.getElem?_eq_some_of_peek?_eq_some anchorFound
      have firstValidNext : Predicate.ValidFor next.file first := by
        simpa [firstValid.2.2] using firstValid.1
      exact (barePredicatesTail_validFor first (next.remainingCount + 1)
        first [] next input.cursor anchor firstValid.2.1 anchorFoundNext
        anchorStart (predicate_cursor_lt_onSuccess firstResult)
        firstValidNext firstValidNext (by simp [List.ValidFor])
        firstValidNext.1.2.1).of_file_eq firstValid.2.2

/-- Bare predicate sequences preserve every ordinary token window. -/
theorem barePredicates_preservesTokenWindow :
    Parser.PreservesTokenWindow barePredicates := by
  intro input
  unfold barePredicates
  have firstShape := predicate_preservesTokenWindow input
  cases firstResult : predicate input with
  | invariant error => trivial
  | reject failure rejected => rw [firstResult] at firstShape; exact firstShape
  | ok first next =>
      rw [firstResult] at firstShape
      exact (barePredicatesTail_preservesTokenWindow first
        (next.remainingCount + 1) first [] next).trans firstShape

theorem barePredicates_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess barePredicates :=
  barePredicates_preservesTokenWindow.preservesTokensOnSuccess

/-- Bare predicate sequences never rewind the cursor. -/
theorem barePredicates_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess barePredicates := by
  intro input values final parsed
  unfold barePredicates at parsed
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first next =>
      simp only [firstResult] at parsed
      exact Nat.le_trans
        (predicate_cursorMonotoneOnSuccess input first next firstResult)
        (barePredicatesTail_cursorMonotoneOnSuccess first
          (next.remainingCount + 1) first [] next values final parsed)

/-- Parenthesized predicate sequences retain delimiters and all predicates. -/
theorem groupedPredicates_validFor :
    groupedPredicates.ValidFor
      (NonemptyDelimitedList.ValidFor Predicate.ValidFor) := by
  unfold groupedPredicates
  apply Parser.bind_validFor_of_value
    (delimited_validFor Predicate.ValidFor .leftParen .rightParen false
      predicate .typeExpr .topLevel predicate_validFor
      predicate_preservesTokensOnSuccess)
  intro values input inputValid valuesValid
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      exact ⟨⟨valuesValid.1, by
          intro value member
          exact valuesValid.2 value (by
            simpa [NonemptyList.toList, elements] using member)⟩,
        inputValid, rfl⟩

/-- Parenthesized predicate sequences preserve every token window. -/
theorem groupedPredicates_preservesTokenWindow :
    Parser.PreservesTokenWindow groupedPredicates := by
  unfold groupedPredicates
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftParen .rightParen false predicate
      .typeExpr .topLevel predicate_preservesTokenWindow)
  intro values input
  cases values.elements with
  | nil => trivial
  | cons head tail => exact ⟨rfl, rfl⟩

theorem groupedPredicates_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess groupedPredicates :=
  groupedPredicates_preservesTokenWindow.preservesTokensOnSuccess

/-- Parenthesized predicate sequences never rewind the cursor. -/
theorem groupedPredicates_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess groupedPredicates := by
  unfold groupedPredicates
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftParen .rightParen false
      predicate .typeExpr .topLevel)
  intro values input result next parsed
  cases elements : values.elements with
  | nil => rw [elements] at parsed; contradiction
  | cons head tail => rw [elements] at parsed; cases parsed; exact Nat.le_refl _

/-- The selected sequence form retains a valid nonempty predicate list. -/
theorem predicateSequence_validFor :
    predicateSequence.ValidFor
      (NonemptyDelimitedList.ValidFor Predicate.ValidFor) := by
  intro input inputValid
  unfold predicateSequence
  split
  · exact Parser.orElse_validFor groupedPredicates_validFor
      barePredicates_validFor input inputValid
  · exact barePredicates_validFor input inputValid

/-- Sequence selection preserves every ordinary token window. -/
theorem predicateSequence_preservesTokenWindow :
    Parser.PreservesTokenWindow predicateSequence := by
  intro input
  unfold predicateSequence
  split
  · exact Parser.orElse_preservesTokenWindow
      groupedPredicates_preservesTokenWindow
      barePredicates_preservesTokenWindow input
  · exact barePredicates_preservesTokenWindow input

theorem predicateSequence_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess predicateSequence :=
  predicateSequence_preservesTokenWindow.preservesTokensOnSuccess

/-- Sequence selection never rewinds the parser cursor. -/
theorem predicateSequence_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess predicateSequence := by
  intro input values next parsed
  unfold predicateSequence at parsed
  split at parsed
  · exact Parser.orElse_cursorMonotoneOnSuccess
      groupedPredicates_cursorMonotoneOnSuccess
      barePredicates_cursorMonotoneOnSuccess input values next parsed
  · exact barePredicates_cursorMonotoneOnSuccess input values next parsed

end PredicateInternals
end Solcore.Syntax.Parser
