import Solcore.Syntax.Parser.Predicate
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.SignatureValidity

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
