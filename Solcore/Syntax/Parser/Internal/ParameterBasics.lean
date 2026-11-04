import Solcore.Syntax.Parser.Types
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Validity

/-!
Basic proofs about the parameter and predicate parsers. `Parser/Signatures` and
`Parser/Blocks` keep theorems beside private helpers and those theorems need this file, so
production code imports it. Keep it small.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateProperties
/-! Provenance and token-carrier contracts for one trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem predicateBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem typeExpr_start_le_following_symbol_end
    (followingSymbol : Symbol) {input after final : State}
    {value : TypeExpr} {following : Token} (afterValid : after.ValidFor)
    (valueResult : typeExpr input = .ok value after)
    (followingResult : symbol followingSymbol .typeExpr after =
      .ok following final) :
    value.span.startByte ≤ following.span.endByte := by
  rcases typeExpr_startsAtCurrentTokenOnSuccess input value after valueResult with
    ⟨first, firstFound, firstStart⟩
  have firstAtInput := State.getElem?_eq_some_of_peek?_eq_some firstFound
  have firstAtAfter : after.tokens[input.cursor]? = some first := by
    rw [typeExpr_preservesTokensOnSuccess input value after valueResult]
    exact firstAtInput
  have followingShape := symbol_ok_state_shape followingSymbol .typeExpr
    followingResult
  have followingAtAfter :=
    State.getElem?_eq_some_of_peek?_eq_some followingShape.1
  rw [← firstStart]
  rcases Nat.eq_or_lt_of_le
      (typeExpr_cursorMonotoneOnSuccess input value after valueResult) with
    cursorEq | cursorLt
  · have tokenEq : first = following := by
      apply Option.some.inj
      rw [← firstAtAfter, ← followingAtAfter, cursorEq]
    rw [tokenEq]
    exact (afterValid.token_span_validFor_of_getElem?_eq_some
      followingAtAfter).2.1
  · have firstNonempty :=
      afterValid.token_span_nonempty_of_getElem?_eq_some firstAtAfter
    have ordered := afterValid.token_end_le_token_start_of_getElem?_lt
      firstAtAfter followingAtAfter cursorLt
    have followingValid :=
      afterValid.token_span_validFor_of_getElem?_eq_some followingAtAfter
    exact Nat.le_trans (Nat.le_of_lt firstNonempty)
      (Nat.le_trans ordered followingValid.2.1)

/-- Predicate parsing retains its subject, trait name, and type arguments. -/
theorem predicate_validFor : predicate.ValidFor Predicate.ValidFor := by
  have weak : predicate.ValidFor (fun _ _ => True) := by
    unfold predicate
    apply Parser.bind_validFor typeExpr_validFor
    intro subject
    apply Parser.bind_validFor (symbol_validFor .colon .typeExpr)
    intro colon
    apply Parser.bind_validFor (identifier_validFor .typeExpr)
    intro traitName
    apply Parser.bind_validFor
      (parseNamedTypeArguments_validFor typeExpr typeExpr_validFor
        typeExpr_preservesTokensOnSuccess)
    intro arguments
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  apply Parser.validFor_of_ok_reject predicate Predicate.ValidFor
  · intro input inputValid result final parsed
    have weakResult := weak input inputValid
    rw [parsed] at weakResult
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
    have subjectValid := typeExpr_validFor input inputValid
    rw [subjectResult] at subjectValid
    have colonValid := symbol_validFor .colon .typeExpr afterSubject
      subjectValid.2.1
    rw [colonResult] at colonValid
    have nameValid := identifier_validFor .typeExpr afterColon colonValid.2.1
    rw [nameResult] at nameValid
    have argumentsValid := parseNamedTypeArguments_validFor typeExpr
      typeExpr_validFor typeExpr_preservesTokensOnSuccess afterName
      nameValid.2.1
    rw [argumentsResult] at argumentsValid
    have subjectValidInput : TypeExpr.ValidFor input.file subject :=
      subjectValid.1
    have nameValidInput : traitName.span.ValidFor input.file := by
      simpa only [Located.ValidFor, colonValid.2.2, subjectValid.2.2] using
        nameValid.1
    have argumentsValidInput : Option.ValidFor
        (NonemptyDelimitedList.ValidFor TypeExpr.ValidFor)
        input.file arguments := by
      simpa [nameValid.2.2, colonValid.2.2, subjectValid.2.2] using
        argumentsValid.1
    have subjectToColon := typeExpr_start_le_following_symbol_end .colon
      subjectValid.2.1 subjectResult colonResult
    have colonShape := symbol_ok_state_shape .colon .typeExpr colonResult
    have colonAdvanced : afterSubject.advance? = some (colon, afterColon) := by
      unfold State.advance?
      rw [colonShape.1, colonShape.2]
      rfl
    rcases identifier_ok_state_shape .typeExpr nameResult with
      ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
    have colonBeforeName : colon.span.endByte ≤ traitName.span.startByte := by
      rw [← nameSpan]
      exact subjectValid.2.1.consumed_end_le_peek_start_after_advance
        colonAdvanced nameFound
    cases finished
    cases arguments with
    | none =>
        have ordered : subject.span.startByte ≤ traitName.span.endByte :=
          Nat.le_trans subjectToColon
            (Nat.le_trans colonBeforeName nameValidInput.2.1)
        exact ⟨⟨SourceSpan.cover_validFor subjectValidInput.span_valid
            nameValidInput ordered, subjectValidInput, nameValidInput,
            by simp, by simp⟩,
          weakResult.2.1, weakResult.2.2⟩
    | some values =>
        have valuesValid : NonemptyDelimitedList.ValidFor TypeExpr.ValidFor
            input.file values := by
          simpa [Option.ValidFor] using argumentsValidInput
        rcases parseNamedTypeArguments_some_startsAtCurrentTokenOnSuccess
            typeExpr argumentsResult with ⟨opening, openingFound, valuesStart⟩
        have nameAtAfter :
            afterName.tokens[afterColon.cursor]? = some nameToken := by
          rw [nameTokens]
          exact State.getElem?_eq_some_of_peek?_eq_some nameFound
        have openingAtAfter :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have nameBeforeValues :
            traitName.span.endByte ≤ values.span.startByte := by
          rw [← valuesStart, ← nameSpan]
          exact nameValid.2.1.token_end_le_token_start_of_getElem?_lt
            nameAtAfter openingAtAfter (by omega)
        have ordered : subject.span.startByte ≤ values.span.endByte :=
          Nat.le_trans subjectToColon
            (Nat.le_trans colonBeforeName
              (Nat.le_trans nameValidInput.2.1
                (Nat.le_trans nameBeforeValues valuesValid.1.2.1)))
        exact ⟨⟨SourceSpan.cover_validFor subjectValidInput.span_valid
            valuesValid.1 ordered, subjectValidInput, nameValidInput,
            by simpa using valuesValid.1,
            by simpa [NonemptyList.ValidFor] using valuesValid.2⟩,
          weakResult.2.1, weakResult.2.2⟩
  · intro input inputValid failure next parsed
    have weakResult := weak input inputValid
    rw [parsed] at weakResult
    exact weakResult

/-- Predicate parsing preserves every ordinary token window. -/
theorem predicate_preservesTokenWindow :
    Parser.PreservesTokenWindow predicate := by
  unfold predicate
  apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
  intro subject
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .colon .typeExpr)
  intro colon
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .typeExpr)
  intro traitName
  apply Parser.bind_preservesTokenWindow
    (parseNamedTypeArguments_preservesTokenWindow typeExpr
      typeExpr_preservesTokenWindow)
  intro arguments
  exact Parser.pure_preservesTokenWindow _

theorem predicate_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess predicate :=
  predicate_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful predicate parsing never rewinds the cursor. -/
theorem predicate_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess predicate := by
  unfold predicate
  apply Parser.bind_cursorMonotoneOnSuccess
    typeExpr_cursorMonotoneOnSuccess
  intro subject
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .colon .typeExpr)
  intro colon
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .typeExpr)
  intro traitName
  apply Parser.bind_cursorMonotoneOnSuccess
    (parseNamedTypeArguments_cursorMonotoneOnSuccess typeExpr)
  intro arguments
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A predicate starts at the first token of its subject type. -/
theorem predicate_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess predicate (·.span) := by
  unfold predicate
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    typeExpr_startsAtCurrentTokenOnSuccess
  intro subject input value final parsed
  rcases predicateBind_ok_components parsed with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceTailProperties
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
end PredicateInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceProperties
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

/-- A bare sequence starts at the first predicate token. -/
theorem barePredicates_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess barePredicates (·.span) := by
  intro input values final parsed
  unfold barePredicates at parsed
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first next =>
      simp only [firstResult] at parsed
      rcases predicate_startsAtCurrentTokenOnSuccess input first next
          firstResult with ⟨token, found, start⟩
      exact ⟨token, found, start.trans
        (barePredicatesTail_preservesFirstStartOnSuccess first
          (next.remainingCount + 1) first [] next values final parsed).symm⟩

/-- A grouped sequence starts at its opening parenthesis. -/
theorem groupedPredicates_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess groupedPredicates (·.span) := by
  unfold groupedPredicates
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .leftParen .rightParen false
      predicate .typeExpr .topLevel)
  intro values input result next parsed
  cases elements : values.elements with
  | nil => rw [elements] at parsed; contradiction
  | cons head tail => rw [elements] at parsed; cases parsed; rfl

/-- Sequence selection starts at its chosen form's current token. -/
theorem predicateSequence_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess predicateSequence (·.span) := by
  intro input values next parsed
  unfold predicateSequence at parsed
  split at parsed
  · exact Parser.orElse_startsAtCurrentTokenOnSuccess
      groupedPredicates_startsAtCurrentTokenOnSuccess
      barePredicates_startsAtCurrentTokenOnSuccess input values next parsed
  · exact barePredicates_startsAtCurrentTokenOnSuccess input values next parsed

end PredicateInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WhereClauseProperties
/-! Public contracts for optional canonical `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `where` parsing retains its marker and every predicate range. -/
theorem whereClause_validFor :
    whereClause.ValidFor (Option.ValidFor WhereClause.ValidFor) := by
  have weak : whereClause.ValidFor (fun _ _ => True) := by
    unfold whereClause
    apply Parser.bind_validFor getState_validFor
    intro observed
    by_cases present : isContextual observed .where
    · simp only [present, if_true]
      apply Parser.bind_validFor (contextual_validFor .where .typeExpr)
      intro marker
      apply Parser.bind_validFor PredicateInternals.predicateSequence_validFor
      intro predicates
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    · simp only [present]
      exact Parser.pure_validFor none (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : whereClause input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok result final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold whereClause getState at stages
      simp only [bind] at stages
      by_cases present : isContextual input .where
      · simp only [present, if_true] at stages
        rcases predicateBind_ok_components stages with
          ⟨marker, afterMarker, markerResult, rest⟩
        rcases predicateBind_ok_components rest with
          ⟨predicates, afterPredicates, predicatesResult, finished⟩
        have markerValid := contextual_validFor .where .typeExpr input
          inputValid
        rw [markerResult] at markerValid
        have predicatesValid := PredicateInternals.predicateSequence_validFor
          afterMarker markerValid.2.1
        rw [predicatesResult] at predicatesValid
        have markerSpanValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerValid.1
        have predicatesValidInput : NonemptyDelimitedList.ValidFor
            Predicate.ValidFor input.file predicates := by
          simpa [markerValid.2.2] using predicatesValid.1
        have markerShape := acceptToken_ok_state_shape
          (.contextual .where) .typeExpr (·.isContextual .where) markerResult
        have markerAdvanced : input.advance? = some (marker, afterMarker) := by
          unfold State.advance?
          rw [markerShape.1, markerShape.2]
          rfl
        rcases PredicateInternals.predicateSequence_startsAtCurrentTokenOnSuccess
            afterMarker predicates afterPredicates predicatesResult with
          ⟨first, firstFound, predicatesStart⟩
        have markerBeforePredicates :=
          inputValid.consumed_end_le_peek_start_after_advance markerAdvanced
            firstFound
        have ordered : marker.span.startByte ≤ predicates.span.endByte :=
          Nat.le_trans markerSpanValid.2.1
            (Nat.le_trans markerBeforePredicates (by
              rw [predicatesStart]
              exact predicatesValidInput.1.2.1))
        have outerValid := SourceSpan.cover_validFor markerSpanValid
          predicatesValidInput.1 ordered
        cases finished
        exact ⟨by
            simpa only [Option.ValidFor] using
              (show WhereClause.ValidFor input.file {
                span := SourceSpan.cover marker.span predicates.span
                predicates := predicates.elements
              } from ⟨outerValid, by
                simpa [NonemptyList.ValidFor] using predicatesValidInput.2⟩),
          weakResult.2.1, weakResult.2.2⟩
      · simp only [present, Bool.false_eq_true, if_false] at stages
        cases stages
        exact ⟨trivial, inputValid, rfl⟩

/-- Optional `where` parsing preserves every ordinary token window. -/
theorem whereClause_preservesTokenWindow :
    Parser.PreservesTokenWindow whereClause := by
  unfold whereClause
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindow
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (contextual_preservesTokenWindow .where .typeExpr)
    intro marker
    apply Parser.bind_preservesTokenWindow
      PredicateInternals.predicateSequence_preservesTokenWindow
    intro predicates
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

theorem whereClause_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess whereClause :=
  whereClause_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional `where` parsing never rewinds the cursor. -/
theorem whereClause_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess whereClause := by
  unfold whereClause
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (contextual_cursorMonotoneOnSuccess .where .typeExpr)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      PredicateInternals.predicateSequence_cursorMonotoneOnSuccess
    intro predicates
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A present `where` clause starts at its contextual marker token. -/
theorem whereClause_some_startsAtCurrentTokenOnSuccess
    {input final : State} {clause : WhereClause}
    (parsed : whereClause input = .ok (some clause) final) :
    ∃ token, input.peek? = some token ∧
      token.span.startByte = clause.span.startByte := by
  unfold whereClause getState at parsed
  simp only [bind] at parsed
  by_cases present : isContextual input .where
  · simp only [present, if_true] at parsed
    rcases predicateBind_ok_components parsed with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases predicateBind_ok_components rest with
      ⟨predicates, afterPredicates, predicatesResult, finished⟩
    rcases contextual_startsAtCurrentTokenOnSuccess .where .typeExpr input
        marker afterMarker markerResult with ⟨token, found, start⟩
    cases finished
    exact ⟨token, found, by simpa [SourceSpan.cover] using start⟩
  · simp only [present, Bool.false_eq_true, if_false] at parsed
    cases parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterProperties
/-! Token-window contracts for recovering function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FunctionParameterInternals

private theorem advance?_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

private theorem getState_preservesTokenWindowForParameter :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForParameter
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

theorem finishRecoveredParameter_validFor (first last : SourceSpan)
    (state : State) (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredParameter first last state).ValidFor state
      FunctionParameter.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredParameter Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩

theorem recoverParameterAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverParameterAux first last fuel state).ValidFor state
        FunctionParameter.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverParameterAux
      split
      · exact finishRecoveredParameter_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredParameter_validFor first last state
              stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

theorem recoverParameter_validFor (state : State)
    (stateValid : state.ValidFor) :
    (recoverParameter state).ValidFor state FunctionParameter.ValidFor := by
  unfold recoverParameter
  cases advanced : state.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := stateValid.advance?_validFor advanced
      have tokenValid := stateValid.peek?_span_validFor shape.1
      have tokenFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverParameterAux_validFor token.span
        (next.remainingCount + 1) token.span next state.cursor token
        nextValid (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using tokenFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

private theorem finishTypedParameter_validFor (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) (input : State) (inputValid : input.ValidFor)
    (spanValid : (SourceSpan.cover start type.span).ValidFor input.file)
    (markerValid : ∀ marker ∈ comptimeMarker,
      marker.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (typeValid : TypeExpr.ValidFor input.file type) :
    (finishTypedParameter start comptimeMarker name type input).ValidFor
      input FunctionParameter.ValidFor := by
  have parameterValid : FunctionParameter.ValidFor input.file {
      span := SourceSpan.cover start type.span
      value := .typed comptimeMarker name type
    } := .typed spanValid markerValid nameValid typeValid
  cases valueEq : type.value <;>
    simp only [finishTypedParameter, valueEq, emitDiagnostic, modifyState,
      bind, pure, Reply.ValidFor]
  case comptime =>
    exact And.intro parameterValid (And.intro
      (inputValid.emit_validFor {
        span := type.span
        kind := .constraintViolation .comptimeTypeInParameter
      } typeValid.span_valid) rfl)
  all_goals exact And.intro parameterValid (And.intro inputValid trivial)

private theorem errorParameter_validFor (span : SourceSpan)
    (constraint : ParseConstraint) (input : State)
    (inputValid : input.ValidFor) (spanValid : span.ValidFor input.file) :
    (errorParameter span constraint input).ValidFor input
      FunctionParameter.ValidFor := by
  unfold errorParameter emitDiagnostic modifyState bind pure Reply.ValidFor
  exact ⟨.error spanValid, inputValid.emit_validFor _ spanValid, rfl⟩

/-- The shared typed-or-error tail retains parameter provenance. -/
theorem namedParameterTail_validFor (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {firstIndex : Nat} {firstToken : Token}
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (markerValid : ∀ marker ∈ comptimeMarker,
      marker.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (errorSpanValid : errorSpan.ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some firstToken)
    (firstSpan : firstToken.span = start)
    (firstBefore : firstIndex < input.cursor) :
    (namedParameterTail start comptimeMarker name errorSpan input).ValidFor
      input FunctionParameter.ValidFor := by
  unfold namedParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    cases colonResult : symbol .colon .parameter input with
    | invariant error => trivial
    | reject failure rejected =>
        have valid := symbol_validFor .colon .parameter input inputValid
        rw [colonResult] at valid
        exact valid
    | ok colon afterColon =>
        have colonValid := symbol_validFor .colon .parameter input inputValid
        rw [colonResult] at colonValid
        simp only
        cases typeResult : typeExpr afterColon with
        | invariant error =>
            change (Reply.invariant error).ValidFor input
              FunctionParameter.ValidFor
            trivial
        | reject failure rejected =>
            change (Reply.reject failure rejected).ValidFor input
              FunctionParameter.ValidFor
            have valid := typeExpr_validFor afterColon colonValid.2.1
            rw [typeResult] at valid
            exact valid.of_file_eq colonValid.2.2
        | ok type afterType =>
            change (finishTypedParameter start comptimeMarker name type
              afterType).ValidFor input FunctionParameter.ValidFor
            have typeReply := typeExpr_validFor afterColon colonValid.2.1
            rw [typeResult] at typeReply
            have typeValid : TypeExpr.ValidFor input.file type := by
              simpa [colonValid.2.2] using typeReply.1
            rcases typeExpr_startsAtCurrentTokenOnSuccess afterColon type
                afterType typeResult with ⟨typeToken, typeFound, typeStart⟩
            have colonShape := symbol_ok_state_shape .colon .parameter
              colonResult
            have typeAtInput :
                input.tokens[afterColon.cursor]? = some typeToken := by
              simpa [colonShape.2] using
                State.getElem?_eq_some_of_peek?_eq_some typeFound
            have beforeType :=
              inputValid.token_end_le_token_start_of_getElem?_lt firstFound
                typeAtInput (Nat.lt_trans firstBefore (by
                  simp [colonShape.2]))
            have ordered : start.startByte ≤ type.span.endByte :=
              Nat.le_trans startValid.2.1 (Nat.le_trans
                (by simpa [firstSpan, typeStart] using beforeType)
                typeValid.span_valid.2.1)
            exact (finishTypedParameter_validFor start comptimeMarker name
              type afterType typeReply.2.1
              (by simpa [typeReply.2.2, colonValid.2.2] using
                (SourceSpan.cover_validFor startValid typeValid.span_valid
                  ordered))
              (by simpa [typeReply.2.2, colonValid.2.2] using markerValid)
              (by simpa [typeReply.2.2, colonValid.2.2] using nameValid)
              (by simpa [typeReply.2.2, colonValid.2.2] using
                typeValid)).of_file_eq
                  (typeReply.2.2.trans colonValid.2.2)
  · simp only [typed]
    change (errorParameter errorSpan .namedParameterRequiresType input).ValidFor
      input FunctionParameter.ValidFor
    exact errorParameter_validFor errorSpan _ input inputValid errorSpanValid

/-- Ordinary named parameters retain name, type, and outer provenance. -/
theorem ordinaryNamedParameter_validFor :
    ordinaryNamedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold ordinaryNamedParameter
  simp only [bind]
  cases nameResult : identifier .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := identifier_validFor .parameter input inputValid
      rw [nameResult] at valid
      exact valid
  | ok name afterName =>
      have nameReply := identifier_validFor .parameter input inputValid
      rw [nameResult] at nameReply
      simp only
      rcases identifier_ok_state_shape .parameter nameResult with
        ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
      have nameAtInput := State.getElem?_eq_some_of_peek?_eq_some nameFound
      have nameAtAfter :
          afterName.tokens[input.cursor]? = some nameToken := by
        simpa [nameTokens] using nameAtInput
      have nameValidAfter : name.span.ValidFor afterName.file := by
        simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
      by_cases warned :
          name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
        let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        change (namedParameterTail name.span none name name.span
          (afterName.emit diagnostic)).ValidFor input
            FunctionParameter.ValidFor
        have emittedValid := nameReply.2.1.emit_validFor diagnostic
          nameValidAfter
        exact (namedParameterTail_validFor name.span none name name.span
          (afterName.emit diagnostic) emittedValid
          (by simpa [State.emit] using nameValidAfter) (by simp)
          (by simpa [State.emit] using nameValidAfter)
          (by simpa [State.emit] using nameValidAfter)
          (by simpa [State.emit] using nameAtAfter) nameSpan
          (by simp [State.emit, nameCursor])).of_file_eq
            (by simpa [State.emit] using nameReply.2.2)
      · simp only [warned]
        exact (namedParameterTail_validFor name.span none name name.span
          afterName nameReply.2.1 nameValidAfter (by simp)
          nameValidAfter nameValidAfter nameAtAfter nameSpan
          (by simp [nameCursor])).of_file_eq nameReply.2.2

/-- Comptime named parameters retain marker, name, type, and outer provenance. -/
theorem comptimeNamedParameter_validFor :
    comptimeNamedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold comptimeNamedParameter
  simp only [bind]
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at valid
      exact valid
  | ok marker afterMarker =>
      have markerReply := contextual_validFor .comptime .parameter input
        inputValid
      rw [markerResult] at markerReply
      simp only
      cases nameResult : identifier .parameter afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := identifier_validFor .parameter afterMarker
            markerReply.2.1
          rw [nameResult] at valid
          exact valid.of_file_eq markerReply.2.2
      | ok name afterName =>
          have nameReply := identifier_validFor .parameter afterMarker
            markerReply.2.1
          rw [nameResult] at nameReply
          simp only
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .parameter (·.isContextual .comptime)
            markerResult
          rcases identifier_ok_state_shape .parameter nameResult with
            ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
          have markerAtInput :=
            State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have markerAtAfter :
              afterName.tokens[input.cursor]? = some marker := by
            simpa [nameTokens, markerShape.2] using markerAtInput
          have nameAtAfterMarker :=
            State.getElem?_eq_some_of_peek?_eq_some nameFound
          have nameAtInput :
              input.tokens[afterMarker.cursor]? = some nameToken := by
            simpa [markerShape.2] using nameAtAfterMarker
          have markerBeforeName :=
            inputValid.token_end_le_token_start_of_getElem?_lt markerAtInput
              nameAtInput (by simp [markerShape.2])
          have markerValidAfter : marker.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2,
              markerReply.2.2] using markerReply.1
          have nameValidAfter : name.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
          have errorSpanValid :
              (SourceSpan.cover marker.span name.span).ValidFor
                afterName.file :=
            SourceSpan.cover_validFor markerValidAfter nameValidAfter
              (Nat.le_trans markerValidAfter.2.1 (Nat.le_trans
                (by simpa [nameSpan] using markerBeforeName)
                nameValidAfter.2.1))
          exact (namedParameterTail_validFor marker.span (some marker.span)
            name (SourceSpan.cover marker.span name.span) afterName
            nameReply.2.1 markerValidAfter (by simp [markerValidAfter])
            nameValidAfter errorSpanValid markerAtAfter rfl
            (by simp [markerShape.2, nameCursor]; omega)).of_file_eq
              (nameReply.2.2.trans markerReply.2.2)

theorem finishTypedParameter_preservesTokenWindow (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) :
    Parser.PreservesTokenWindow
      (finishTypedParameter start comptimeMarker name type) := by
  unfold finishTypedParameter
  split
  · apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow _

theorem errorParameter_preservesTokenWindow (span : SourceSpan)
    (constraint : ParseConstraint) :
    Parser.PreservesTokenWindow (errorParameter span constraint) := by
  unfold errorParameter
  apply Parser.bind_preservesTokenWindow
    (emitDiagnostic_preservesTokenWindowForParameter _)
  intro _
  exact Parser.pure_preservesTokenWindow _

theorem namedParameterTail_preservesTokenWindow (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) :
    Parser.PreservesTokenWindow
      (namedParameterTail start comptimeMarker name errorSpan) := by
  unfold namedParameterTail
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForParameter
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colon .parameter)
    intro _
    apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
    intro type
    exact finishTypedParameter_preservesTokenWindow start
      comptimeMarker name type
  · simp only [typed]
    exact errorParameter_preservesTokenWindow errorSpan _

theorem ordinaryNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    exact namedParameterTail_preservesTokenWindow
      name.span none name name.span
  · simp only [warned]
    exact namedParameterTail_preservesTokenWindow
      name.span none name name.span

theorem comptimeNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .comptime .parameter)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  exact namedParameterTail_preservesTokenWindow marker.span
    (some marker.span) name (SourceSpan.cover marker.span name.span)

/-- The non-recovering parameter choice preserves complete provenance. -/
theorem namedParameterCore_validFor :
    namedParameterCore.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_validFor input inputValid
    · exact ordinaryNamedParameter_validFor input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_validFor input inputValid

theorem namedParameterCore_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameterCore := by
  intro input
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_preservesTokenWindow input
    · exact ordinaryNamedParameter_preservesTokenWindow input
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_preservesTokenWindow input

theorem recoverParameterAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverParameterAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverParameterAux
      split
      · unfold finishRecoveredParameter Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredParameter Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverParameter := by
  intro input
  unfold recoverParameter
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      exact (recoverParameterAux_preservesTokenWindow token.span token.span
        (afterToken.remainingCount + 1) afterToken).trans (by
          simp [(advance?_state_shape advanced).2])

private theorem finishTypedParameter_ok_state_shape (start : SourceSpan)
    (marker : Option SourceSpan) (name : Identifier) (type : TypeExpr)
    {input final : State} {value : FunctionParameter}
    (parsed : finishTypedParameter start marker name type input = .ok value final) :
    input.cursor = final.cursor ∧ start.startByte = value.span.startByte := by
  cases valueEq : type.value <;>
    simp only [finishTypedParameter, valueEq, emitDiagnostic, modifyState,
      bind, pure] at parsed <;> cases parsed <;> exact ⟨rfl, rfl⟩

theorem errorParameter_ok_state_shape (span : SourceSpan)
    (constraint : ParseConstraint) {input final : State}
    {value : FunctionParameter}
    (parsed : errorParameter span constraint input = .ok value final) :
    input.cursor = final.cursor ∧ value.span = span := by
  unfold errorParameter emitDiagnostic modifyState at parsed
  simp only [bind, pure] at parsed
  cases parsed
  exact ⟨rfl, rfl⟩

theorem namedParameterTail_ok_state_shape (start : SourceSpan)
    (marker : Option SourceSpan) (name : Identifier) (errorSpan : SourceSpan)
    (errorStart : errorSpan.startByte = start.startByte) {input final : State}
    {value : FunctionParameter}
    (parsed : namedParameterTail start marker name errorSpan input = .ok value final) :
    input.cursor ≤ final.cursor ∧ start.startByte = value.span.startByte := by
  unfold namedParameterTail getState at parsed
  simp only [bind] at parsed
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at parsed
    cases colonResult : symbol .colon .parameter input with
    | ok colon afterColon =>
        simp only [colonResult] at parsed
        cases typeResult : typeExpr afterColon with
        | ok type afterType =>
            simp only [typeResult] at parsed
            have finished := finishTypedParameter_ok_state_shape
              start marker name type parsed
            exact ⟨Nat.le_trans
              (symbol_cursorMonotoneOnSuccess .colon .parameter
                input colon afterColon colonResult)
              (Nat.le_trans (typeExpr_cursorMonotoneOnSuccess
                afterColon type afterType typeResult)
                (Nat.le_of_eq finished.1)), finished.2⟩
        | reject failure rejected => simp [typeResult] at parsed
        | invariant error => simp [typeResult] at parsed
    | reject failure rejected => simp [colonResult] at parsed
    | invariant error => simp [colonResult] at parsed
  · simp only [typed] at parsed
    have failed := errorParameter_ok_state_shape errorSpan
      .namedParameterRequiresType parsed
    exact ⟨Nat.le_of_eq failed.1,
      errorStart.symm.trans (congrArg _ failed.2).symm⟩

private theorem recoverParameterAux_ok_state_shape (first last : SourceSpan) :
    ∀ fuel, ∀ {input final : State} {value : FunctionParameter},
      recoverParameterAux first last fuel input = .ok value final →
      input.cursor ≤ final.cursor ∧ first.startByte = value.span.startByte := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverParameterAux]
  | succ fuel inductionHypothesis =>
      intro input final value parsed
      unfold recoverParameterAux at parsed
      split at parsed
      · unfold finishRecoveredParameter at parsed
        cases parsed
        exact ⟨Nat.le_refl _, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredParameter at parsed
            cases parsed
            exact ⟨Nat.le_refl _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at parsed
            have recursive := inductionHypothesis token.span parsed
            exact ⟨Nat.le_trans (by
              simp [(advance?_state_shape advanced).2]) recursive.1,
              recursive.2⟩

theorem recoverParameter_ok_state_shape {input final : State}
    {value : FunctionParameter} (parsed : recoverParameter input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold recoverParameter at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at parsed
      have recovered := recoverParameterAux_ok_state_shape token.span
        token.span (afterToken.remainingCount + 1) parsed
      exact ⟨Nat.le_trans (by simp [(advance?_state_shape advanced).2])
        recovered.1, token, (advance?_state_shape advanced).1, recovered.2⟩

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem ofFunctionParameter_validFor {file : SourceFile}
    {parameter : FunctionParameter}
    (valid : FunctionParameter.ValidFor file parameter) :
    LambdaParameter.ValidFor file (ofFunctionParameter parameter) := by
  cases valid with
  | typed spanValid markerValid nameValid typeValid =>
      exact .typed spanValid markerValid nameValid typeValid
  | error spanValid => exact .error spanValid

private theorem mappedFunctionParameter_validFor (parser : Parser FunctionParameter)
    {input : State}
    (valid : (parser input).ValidFor input FunctionParameter.ValidFor) :
    ((do pure (ofFunctionParameter (← parser))) input).ValidFor input
      LambdaParameter.ValidFor := by
  simp only [bind]
  cases parsed : parser input with
  | invariant error => trivial
  | reject failure rejected =>
      simp only [parsed, Reply.ValidFor] at valid ⊢
      exact valid
  | ok parameter final =>
      simp only [parsed, Reply.ValidFor] at valid ⊢
      exact ⟨ofFunctionParameter_validFor valid.1, valid.2.1, valid.2.2⟩

theorem ordinaryLambdaParameterTail_validFor (name : Identifier)
    {firstIndex : Nat} {firstToken : Token} (input : State)
    (inputValid : input.ValidFor) (nameValid : name.span.ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some firstToken)
    (firstSpan : firstToken.span = name.span)
    (firstBefore : firstIndex < input.cursor) :
    (ordinaryLambdaParameterTail name input).ValidFor input
      LambdaParameter.ValidFor := by
  unfold ordinaryLambdaParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    have valid := FunctionParameterInternals.namedParameterTail_validFor name.span
      none name name.span input inputValid nameValid (by simp) nameValid
      nameValid firstFound firstSpan firstBefore
    exact mappedFunctionParameter_validFor _ valid
  · simp only [typed, pure, Reply.ValidFor]
    exact ⟨.inferred nameValid nameValid, inputValid, rfl⟩

theorem comptimeLambdaParameterTail_validFor (marker : Token)
    (name : Identifier) {firstIndex : Nat} (input : State)
    (inputValid : input.ValidFor) (markerValid : marker.span.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (spanValid : (SourceSpan.cover marker.span name.span).ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some marker)
    (firstBefore : firstIndex < input.cursor) :
    (comptimeLambdaParameterTail marker name input).ValidFor input
      LambdaParameter.ValidFor := by
  unfold comptimeLambdaParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    have valid := FunctionParameterInternals.namedParameterTail_validFor marker.span
      (some marker.span) name (SourceSpan.cover marker.span name.span)
      input inputValid markerValid (by simp [markerValid]) nameValid spanValid
      firstFound rfl firstBefore
    exact mappedFunctionParameter_validFor _ valid
  · simp only [typed, Bool.false_eq_true, if_false]
    have valid := FunctionParameterInternals.errorParameter_validFor
      (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input inputValid spanValid
    exact mappedFunctionParameter_validFor _ valid

theorem ordinaryLambdaParameter_validFor :
    ordinaryLambdaParameter.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold ordinaryLambdaParameter
  simp only [bind]
  cases nameResult : identifier .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := identifier_validFor .parameter input inputValid
      rw [nameResult] at valid
      exact valid
  | ok name afterName =>
      have nameReply := identifier_validFor .parameter input inputValid
      rw [nameResult] at nameReply
      simp only
      rcases identifier_ok_state_shape .parameter nameResult with
        ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
      have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
      have nameAtAfter : afterName.tokens[input.cursor]? = some nameToken := by
        simpa [nameTokens] using nameAt
      have nameValid : name.span.ValidFor afterName.file := by
        simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
        let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        change (ordinaryLambdaParameterTail name
          (afterName.emit diagnostic)).ValidFor input LambdaParameter.ValidFor
        have emitted := nameReply.2.1.emit_validFor diagnostic nameValid
        exact (ordinaryLambdaParameterTail_validFor name
          (afterName.emit diagnostic) emitted
          (by simpa [State.emit] using nameValid)
          (by simpa [State.emit] using nameAtAfter) nameSpan
          (by simp [State.emit, nameCursor])).of_file_eq
            (by simpa [State.emit] using nameReply.2.2)
      · simp only [warned]
        exact (ordinaryLambdaParameterTail_validFor name afterName
          nameReply.2.1 nameValid nameAtAfter nameSpan
          (by simp [nameCursor])).of_file_eq nameReply.2.2

theorem comptimeLambdaParameter_validFor :
    comptimeLambdaParameter.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold comptimeLambdaParameter
  simp only [bind]
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at valid
      exact valid
  | ok marker afterMarker =>
      have markerReply := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at markerReply
      simp only
      cases nameResult : identifier .parameter afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := identifier_validFor .parameter afterMarker markerReply.2.1
          rw [nameResult] at valid
          exact valid.of_file_eq markerReply.2.2
      | ok name afterName =>
          have nameReply := identifier_validFor .parameter afterMarker markerReply.2.1
          rw [nameResult] at nameReply
          simp only
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .parameter (·.isContextual .comptime)
            markerResult
          rcases identifier_ok_state_shape .parameter nameResult with
            ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
          have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have markerAtAfter : afterName.tokens[input.cursor]? = some marker := by
            simpa [nameTokens, markerShape.2] using markerAt
          have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
          have nameAtInput : input.tokens[afterMarker.cursor]? = some nameToken := by
            simpa [markerShape.2] using nameAt
          have beforeName := inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt nameAtInput (by simp [markerShape.2])
          have markerValid : marker.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2, markerReply.2.2]
              using markerReply.1
          have nameValid : name.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
          have spanValid : (SourceSpan.cover marker.span name.span).ValidFor
              afterName.file := SourceSpan.cover_validFor markerValid nameValid
            (Nat.le_trans markerValid.2.1 (Nat.le_trans
              (by simpa [nameSpan] using beforeName) nameValid.2.1))
          exact (comptimeLambdaParameterTail_validFor marker name afterName
            nameReply.2.1 markerValid nameValid spanValid markerAtAfter
            (by simp [markerShape.2, nameCursor]; omega)).of_file_eq
              (nameReply.2.2.trans markerReply.2.2)

theorem lambdaParameterCore_validFor :
    lambdaParameterCore.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_validFor input inputValid
    · exact ordinaryLambdaParameter_validFor input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameter_validFor input inputValid

theorem recoverLambdaParameter_validFor (input : State)
    (inputValid : input.ValidFor) :
    (recoverLambdaParameter input).ValidFor input LambdaParameter.ValidFor := by
  unfold recoverLambdaParameter
  cases parsed : FunctionParameterInternals.recoverParameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := FunctionParameterInternals.recoverParameter_validFor input inputValid
      rw [parsed] at valid
      exact valid
  | ok recovered final =>
      have valid := FunctionParameterInternals.recoverParameter_validFor input inputValid
      rw [parsed] at valid
      exact ⟨.error valid.1.span_valid, valid.2.1, valid.2.2⟩

theorem ordinaryLambdaParameterTail_preservesTokenWindow (name : Identifier) :
    Parser.PreservesTokenWindow (ordinaryLambdaParameterTail name) := by
  unfold ordinaryLambdaParameterTail
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindow
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_preservesTokenWindow
      (FunctionParameterInternals.namedParameterTail_preservesTokenWindow
        name.span none name name.span)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · simp only [typed]
    exact Parser.pure_preservesTokenWindow _

theorem comptimeLambdaParameterTail_preservesTokenWindow (marker : Token)
    (name : Identifier) : Parser.PreservesTokenWindow
      (comptimeLambdaParameterTail marker name) := by
  unfold comptimeLambdaParameterTail
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindow
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_preservesTokenWindow
      (FunctionParameterInternals.namedParameterTail_preservesTokenWindow
        marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span))
    intro _
    exact Parser.pure_preservesTokenWindow _
  · simp only [typed]
    apply Parser.bind_preservesTokenWindow
      (FunctionParameterInternals.errorParameter_preservesTokenWindow
        (SourceSpan.cover marker.span name.span) _)
    intro _
    exact Parser.pure_preservesTokenWindow _

theorem ordinaryLambdaParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow ordinaryLambdaParameter := by
  unfold ordinaryLambdaParameter
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindow _)
    intro _
    exact ordinaryLambdaParameterTail_preservesTokenWindow name
  · simp only [warned]
    exact ordinaryLambdaParameterTail_preservesTokenWindow name

theorem comptimeLambdaParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow comptimeLambdaParameter := by
  unfold comptimeLambdaParameter
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .comptime .parameter)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  exact comptimeLambdaParameterTail_preservesTokenWindow marker name

theorem lambdaParameterCore_preservesTokenWindow :
    Parser.PreservesTokenWindow lambdaParameterCore := by
  intro input
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_preservesTokenWindow input
    · exact ordinaryLambdaParameter_preservesTokenWindow input
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameter_preservesTokenWindow input

theorem recoverLambdaParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverLambdaParameter := by
  intro input
  unfold recoverLambdaParameter
  have shape :=
    FunctionParameterInternals.recoverParameter_preservesTokenWindow input
  cases parsed : FunctionParameterInternals.recoverParameter input <;>
    rw [parsed] at shape <;> exact shape

private theorem ordinaryLambdaParameterTail_ok_state_shape (name : Identifier)
    {input final : State} {value : LambdaParameter}
    (parsed : ordinaryLambdaParameterTail name input = .ok value final) :
    input.cursor ≤ final.cursor ∧ name.span.startByte = value.span.startByte := by
  unfold ordinaryLambdaParameterTail getState at parsed
  simp only [bind] at parsed
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at parsed
    cases tailResult : FunctionParameterInternals.namedParameterTail
        name.span none name name.span input with
    | ok parameter afterParameter =>
        simp only [tailResult, pure] at parsed
        have shape := FunctionParameterInternals.namedParameterTail_ok_state_shape
          name.span none name name.span rfl tailResult
        cases parsed
        exact shape
    | reject failure rejected => simp [tailResult] at parsed
    | invariant error => simp [tailResult] at parsed
  · simp only [typed, pure] at parsed
    cases parsed
    exact ⟨Nat.le_refl _, rfl⟩

private theorem comptimeLambdaParameterTail_ok_state_shape (marker : Token)
    (name : Identifier) {input final : State} {value : LambdaParameter}
    (parsed : comptimeLambdaParameterTail marker name input = .ok value final) :
    input.cursor ≤ final.cursor ∧ marker.span.startByte = value.span.startByte := by
  unfold comptimeLambdaParameterTail getState at parsed
  simp only [bind] at parsed
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at parsed
    cases tailResult : FunctionParameterInternals.namedParameterTail marker.span
        (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | ok parameter afterParameter =>
        simp only [tailResult, pure] at parsed
        have shape := FunctionParameterInternals.namedParameterTail_ok_state_shape
          marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) rfl tailResult
        cases parsed
        exact shape
    | reject failure rejected => simp [tailResult] at parsed
    | invariant error => simp [tailResult] at parsed
  · simp only [typed] at parsed
    cases errorResult : FunctionParameterInternals.errorParameter
        (SourceSpan.cover marker.span name.span)
          .comptimeParameterRequiresType input with
    | ok parameter afterParameter =>
        simp only [pure] at parsed
        cases parsed
        exact ⟨by simp [State.emit], rfl⟩
    | reject failure rejected => simp [errorResult] at parsed
    | invariant error => simp [errorResult] at parsed

private theorem ordinaryLambdaParameter_ok_state_shape {input final : State}
    {value : LambdaParameter} (parsed : ordinaryLambdaParameter input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold ordinaryLambdaParameter at parsed
  simp only [bind] at parsed
  cases nameResult : identifier .parameter input with
  | ok name afterName =>
      simp only [nameResult] at parsed
      rcases identifier_ok_state_shape .parameter nameResult with
        ⟨token, found, nameSpan, _tokens, _cursor⟩
      have nameMonotone := identifier_cursorMonotoneOnSuccess .parameter
        input name afterName nameResult
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState] at parsed
        have tail := ordinaryLambdaParameterTail_ok_state_shape name parsed
        exact ⟨Nat.le_trans nameMonotone (by
          simpa [State.emit] using tail.1), token, found,
          (congrArg SourceSpan.startByte nameSpan).trans tail.2⟩
      · simp only [warned] at parsed
        have tail := ordinaryLambdaParameterTail_ok_state_shape name parsed
        exact ⟨Nat.le_trans nameMonotone tail.1, token, found,
          (congrArg SourceSpan.startByte nameSpan).trans tail.2⟩
  | reject failure rejected => simp [nameResult] at parsed
  | invariant error => simp [nameResult] at parsed

private theorem comptimeLambdaParameter_ok_state_shape {input final : State}
    {value : LambdaParameter} (parsed : comptimeLambdaParameter input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold comptimeLambdaParameter at parsed
  simp only [bind] at parsed
  cases markerResult : contextual .comptime .parameter input with
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases nameResult : identifier .parameter afterMarker with
      | ok name afterName =>
          simp only [nameResult] at parsed
          have tail := comptimeLambdaParameterTail_ok_state_shape
            marker name parsed
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .parameter (fun kind =>
              kind.isContextual .comptime) markerResult
          exact ⟨Nat.le_trans
            (contextual_cursorMonotoneOnSuccess .comptime .parameter
              input marker afterMarker markerResult)
            (Nat.le_trans (identifier_cursorMonotoneOnSuccess .parameter
              afterMarker name afterName nameResult) tail.1),
            marker, markerShape.1, tail.2⟩
      | reject failure rejected => simp [nameResult] at parsed
      | invariant error => simp [nameResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | invariant error => simp [markerResult] at parsed

theorem lambdaParameterCore_ok_state_shape {input final : State}
    {value : LambdaParameter} (parsed : lambdaParameterCore input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold lambdaParameterCore at parsed
  split at parsed
  · simp only [Bool.and_true] at parsed
    split at parsed
    · exact comptimeLambdaParameter_ok_state_shape parsed
    · exact ordinaryLambdaParameter_ok_state_shape parsed
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at parsed
    exact ordinaryLambdaParameter_ok_state_shape parsed

theorem recoverLambdaParameter_ok_state_shape {input final : State}
    {value : LambdaParameter} (parsed : recoverLambdaParameter input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold recoverLambdaParameter at parsed
  cases recovery : FunctionParameterInternals.recoverParameter input with
  | ok recovered next =>
      simp only [recovery] at parsed
      have shape := FunctionParameterInternals.recoverParameter_ok_state_shape
        recovery
      cases parsed
      exact shape
  | reject failure next => simp [recovery] at parsed
  | invariant error => simp [recovery] at parsed

end LambdaParameterInternals

/-- Named parameters retain provenance through parsing and recovery. -/
theorem namedParameter_validFor :
    namedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold namedParameter
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter next =>
      have valid := FunctionParameterInternals.namedParameterCore_validFor
        input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid :=
        FunctionParameterInternals.namedParameterCore_validFor input inputValid
      rw [coreResult] at coreValid
      have coreShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)).ValidFor input
            FunctionParameter.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have failureValid : failure.span.ValidFor rewound.file := by
          simpa [rewound, coreValid.2.2] using coreValid.1
        have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (FunctionParameterInternals.recoverParameter_validFor
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)

/-- Function-parameter parsing preserves every ordinary token window. -/
theorem namedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameter := by
  intro input
  unfold namedParameter
  have coreShape :=
    FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := ⟨by simp [rewound, coreShape.1],
        by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (FunctionParameterInternals.recoverParameter_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

/-- Successful function-parameter parsing retains the token carrier. -/
theorem namedParameter_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess namedParameter :=
  namedParameter_preservesTokenWindow.preservesTokensOnSuccess

/-- Lambda parameters retain provenance through parsing and recovery. -/
theorem lambdaParameter_validFor :
    lambdaParameter.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold lambdaParameter
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter next =>
      have valid := LambdaParameterInternals.lambdaParameterCore_validFor
        input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := LambdaParameterInternals.lambdaParameterCore_validFor
        input inputValid
      rw [coreResult] at coreValid
      have coreShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)).ValidFor input
            LambdaParameter.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have failureValid : failure.span.ValidFor rewound.file := by
          simpa [rewound, coreValid.2.2] using coreValid.1
        have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (LambdaParameterInternals.recoverLambdaParameter_validFor
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)

/-- Lambda-parameter recovery preserves every ordinary token window. -/
theorem lambdaParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow lambdaParameter := by
  intro input
  unfold lambdaParameter
  have coreShape :=
    LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := ⟨by simp [rewound, coreShape.1],
        by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (LambdaParameterInternals.recoverLambdaParameter_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

theorem lambdaParameter_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess lambdaParameter :=
  lambdaParameter_preservesTokenWindow.preservesTokensOnSuccess

theorem lambdaParameter_ok_state_shape {input final : State}
    {value : LambdaParameter} (parsed : lambdaParameter input =
      .ok value final) : input.cursor ≤ final.cursor ∧
      ∃ token, input.peek? = some token ∧
        token.span.startByte = value.span.startByte := by
  unfold lambdaParameter at parsed
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | invariant error => simp [coreResult] at parsed
  | ok coreValue afterCore =>
      simp only [coreResult] at parsed
      have shape := LambdaParameterInternals.lambdaParameterCore_ok_state_shape
        coreResult
      cases parsed
      exact shape
  | reject failure failedState =>
      simp only [coreResult] at parsed
      have coreShape :=
        LambdaParameterInternals.lambdaParameterCore_preservesTokenWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok value final at parsed
      split at parsed
      · contradiction
      · have recovered :=
          LambdaParameterInternals.recoverLambdaParameter_ok_state_shape parsed
        rcases recovered.2 with ⟨token, found, start⟩
        refine ⟨by simpa [State.emit, rewound] using recovered.1,
          token, ?_, start⟩
        unfold State.peek? at found ⊢
        simpa [State.emit, rewound, coreShape.1, coreShape.2] using found

/-- Successful lambda-parameter parsing never rewinds the caller. -/
theorem lambdaParameter_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess lambdaParameter :=
  fun _ _ _ parsed => (lambdaParameter_ok_state_shape parsed).1

/-- Successful lambda parameters start at the caller's current token. -/
theorem lambdaParameter_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess lambdaParameter (fun value =>
      value.span) :=
  fun _ _ _ parsed => (lambdaParameter_ok_state_shape parsed).2

end Solcore.Syntax.Parser
end
