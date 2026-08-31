import Solcore.Syntax.Parser.PredicateProperties

/-! Internal contracts for the bare-predicate sequence loop. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace PredicateInternals

private theorem sequenceValue_validFor (first : Predicate)
    (tailRev : List Predicate) (lastSpan : SourceSpan)
    {file : SourceFile} (firstValid : Predicate.ValidFor file first)
    (tailValid : List.ValidFor Predicate.ValidFor file tailRev)
    (lastValid : lastSpan.ValidFor file)
    (ordered : first.span.startByte ≤ lastSpan.endByte) :
    NonemptyDelimitedList.ValidFor Predicate.ValidFor file {
      span := SourceSpan.cover first.span lastSpan
      elements := { head := first, tail := tailRev.reverse }
    } := by
  refine ⟨SourceSpan.cover_validFor firstValid.1 lastValid ordered, ?_⟩
  intro value member
  rcases List.mem_cons.mp member with rfl | member
  · exact firstValid
  · exact tailValid value (by simpa using member)

theorem predicate_cursor_lt_onSuccess {input next : State}
    {value : Predicate} (parsed : predicate input = .ok value next) :
    input.cursor < next.cursor := by
  have stages := parsed
  unfold predicate at stages
  rcases predicateBind_ok_components stages with
    ⟨subject, afterSubject, subjectResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  exact Nat.lt_of_le_of_lt
    (typeExpr_cursorMonotoneOnSuccess input subject afterSubject subjectResult)
    (Nat.lt_of_lt_of_le
      (acceptToken_cursor_lt_onSuccess (.symbol .colon) .typeExpr
        (· == .symbol .colon) colonResult)
      (Nat.le_trans
        (identifier_cursorMonotoneOnSuccess .typeExpr afterColon
          traitName afterName nameResult)
        (parseNamedTypeArguments_cursorMonotoneOnSuccess typeExpr
          afterName arguments next argumentsResult)))

theorem barePredicatesTail_validFor (first : Predicate) :
    ∀ fuel last tailRev input anchorIndex anchor,
      input.ValidFor →
      input.tokens[anchorIndex]? = some anchor →
      anchor.span.startByte = first.span.startByte →
      anchorIndex < input.cursor →
      Predicate.ValidFor input.file first →
      Predicate.ValidFor input.file last →
      List.ValidFor Predicate.ValidFor input.file tailRev →
      first.span.startByte ≤ last.span.endByte →
      (barePredicatesTail first fuel last tailRev input).ValidFor input
        (NonemptyDelimitedList.ValidFor Predicate.ValidFor) := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input anchorIndex anchor inputValid anchorFound
        anchorStart anchorBefore firstValid lastValid tailValid ordered
      unfold barePredicatesTail
      split
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error => trivial
        | reject failure rejected =>
            have valid := symbol_validFor .comma .typeExpr input inputValid
            rw [commaResult] at valid
            exact valid
        | ok comma afterComma =>
            have commaValid := symbol_validFor .comma .typeExpr input inputValid
            rw [commaResult] at commaValid
            have commaShape := symbol_ok_state_shape .comma .typeExpr commaResult
            have anchorFoundAfter :
                afterComma.tokens[anchorIndex]? = some anchor := by
              simpa [commaShape.2] using anchorFound
            have anchorBeforeAfter : anchorIndex < afterComma.cursor := by
              simpa [commaShape.2] using Nat.lt_succ_of_lt anchorBefore
            simp only
            split
            · cases valueResult : predicate afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  have valid := predicate_validFor afterComma commaValid.2.1
                  rw [valueResult] at valid
                  exact valid.of_file_eq commaValid.2.2
              | ok value next =>
                  have valueValid := predicate_validFor afterComma
                    commaValid.2.1
                  rw [valueResult] at valueValid
                  have anchorFoundNext :
                      next.tokens[anchorIndex]? = some anchor := by
                    rw [predicate_preservesTokensOnSuccess afterComma value
                      next valueResult]
                    exact anchorFoundAfter
                  have firstValidNext : Predicate.ValidFor next.file first := by
                    simpa [valueValid.2.2, commaValid.2.2] using firstValid
                  have lastValidNext : Predicate.ValidFor next.file value := by
                    simpa [valueValid.2.2] using valueValid.1
                  have tailValidNext : List.ValidFor Predicate.ValidFor
                      next.file (value :: tailRev) := by
                    intro retained member
                    rcases List.mem_cons.mp member with rfl | member
                    · exact lastValidNext
                    · simpa [valueValid.2.2, commaValid.2.2] using
                        tailValid retained member
                  rcases predicate_startsAtCurrentTokenOnSuccess afterComma
                      value next valueResult with ⟨token, found, valueStart⟩
                  have anchorAt := anchorFoundAfter
                  have valueAt :=
                    State.getElem?_eq_some_of_peek?_eq_some found
                  have separated :=
                    commaValid.2.1.token_end_le_token_start_of_getElem?_lt
                      anchorAt valueAt anchorBeforeAfter
                  have nextOrdered :
                      first.span.startByte ≤ value.span.endByte := by
                    rw [← anchorStart]
                    exact Nat.le_trans
                      (commaValid.2.1.token_span_validFor_of_getElem?_eq_some
                        anchorAt).2.1
                      (Nat.le_trans separated
                        (Nat.le_trans (Nat.le_of_eq valueStart)
                          lastValidNext.1.2.1))
                  exact (inductionHypothesis value (value :: tailRev) next
                    anchorIndex anchor valueValid.2.1 anchorFoundNext
                    anchorStart (Nat.lt_of_lt_of_le anchorBeforeAfter
                      (predicate_cursorMonotoneOnSuccess afterComma value next
                        valueResult)) firstValidNext lastValidNext
                    tailValidNext nextOrdered).of_file_eq
                      (valueValid.2.2.trans commaValid.2.2)
            · have commaSpanValid : comma.span.ValidFor input.file := by
                simpa only [Located.ValidFor] using commaValid.1
              have commaFound :=
                State.getElem?_eq_some_of_peek?_eq_some commaShape.1
              have separated := inputValid.token_end_le_token_start_of_getElem?_lt
                anchorFound commaFound anchorBefore
              have coverOrdered :
                  first.span.startByte ≤ comma.span.endByte := by
                rw [← anchorStart]
                exact Nat.le_trans
                  (inputValid.token_span_validFor_of_getElem?_eq_some
                    anchorFound).2.1
                  (Nat.le_trans separated commaSpanValid.2.1)
              exact ⟨sequenceValue_validFor first tailRev comma.span
                  firstValid tailValid commaSpanValid coverOrdered,
                commaValid.2.1, commaValid.2.2⟩
      · exact ⟨sequenceValue_validFor first tailRev last.span firstValid
            tailValid lastValid.1 ordered, inputValid, rfl⟩

theorem barePredicatesTail_preservesTokenWindow (first : Predicate) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (barePredicatesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      simp [barePredicatesTail, Reply.PreservesTokenWindow]
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold barePredicatesTail
      split
      · have commaShape := symbol_preservesTokenWindow .comma .typeExpr input
        cases commaResult : symbol .comma .typeExpr input with
        | invariant error => trivial
        | reject failure rejected => rw [commaResult] at commaShape; exact commaShape
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            simp only
            split
            · have valueShape := predicate_preservesTokenWindow afterComma
              cases valueResult : predicate afterComma with
              | invariant error => trivial
              | reject failure rejected =>
                  rw [valueResult] at valueShape
                  exact valueShape.trans commaShape
              | ok value next =>
                  rw [valueResult] at valueShape
                  exact (inductionHypothesis value (value :: tailRev) next).trans
                    (valueShape.trans commaShape)
            · exact commaShape
      · exact ⟨rfl, rfl⟩

theorem barePredicatesTail_cursorMonotoneOnSuccess
    (first : Predicate) : ∀ fuel last tailRev,
      Parser.CursorMonotoneOnSuccess
        (barePredicatesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero => intros _ _ input value next parsed; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input result final parsed
      unfold barePredicatesTail at parsed
      split at parsed
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            have commaMonotone := symbol_cursorMonotoneOnSuccess .comma
              .typeExpr input comma afterComma commaResult
            split at parsed
            · cases valueResult : predicate afterComma with
              | invariant error => simp [valueResult] at parsed
              | reject failure rejected => simp [valueResult] at parsed
              | ok value next =>
                  simp only [valueResult] at parsed
                  exact Nat.le_trans commaMonotone (Nat.le_trans
                    (predicate_cursorMonotoneOnSuccess afterComma value next
                      valueResult)
                    (inductionHypothesis value (value :: tailRev) next result
                      final parsed))
            · cases parsed
              exact commaMonotone
      · cases parsed
        exact Nat.le_refl _

/-- Every successful bare loop keeps the first predicate's start. -/
theorem barePredicatesTail_preservesFirstStartOnSuccess
    (first : Predicate) : ∀ fuel last tailRev input values final,
      barePredicatesTail first fuel last tailRev input = .ok values final →
      values.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input values final parsed
      unfold barePredicatesTail at parsed
      split at parsed
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · cases valueResult : predicate afterComma with
              | invariant error => simp [valueResult] at parsed
              | reject failure rejected => simp [valueResult] at parsed
              | ok value next =>
                  simp only [valueResult] at parsed
                  exact inductionHypothesis value (value :: tailRev) next
                    values final parsed
            · cases parsed
              rfl
      · cases parsed
        rfl
