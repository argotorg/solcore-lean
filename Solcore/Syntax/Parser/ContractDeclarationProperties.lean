import Solcore.Syntax.Parser.ContractBodyProperties

/-! Conditional contracts for the outer canonical contract declaration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- The body-parser boundary required by the outer declaration proof. -/
structure ContractBodyParserInputs : Prop where
  validFor : contractBody.ValidFor ContractBody.ValidFor
  preservesTokenWindow : Parser.PreservesTokenWindow contractBody
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractBody
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractBody (·.span)

/-- The complete outer declaration contract produced from a body boundary. -/
structure ContractDeclParserContract : Prop where
  validFor : contractDecl.ValidFor
    (ContractDecl.ValidFor CoreStatement.ValidFor CoreExpr.ValidFor)
  preservesTokenWindow : Parser.PreservesTokenWindow contractDecl
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess contractDecl
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess contractDecl (·.span)
  cursorLtOnSuccess : ∀ {input final : State} {declaration : ContractDecl},
    contractDecl input = .ok declaration final → input.cursor < final.cursor

theorem ContractDeclParserContract.preservesTokensOnSuccess
    (contract : ContractDeclParserContract) :
    Parser.PreservesTokensOnSuccess contractDecl :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

private theorem contractBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
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

/-- The outer contract declaration composes entirely from its body boundary. -/
theorem contractDecl_contract (bodyInputs : ContractBodyParserInputs) :
    ContractDeclParserContract := {
  validFor := by
    have weak : contractDecl.ValidFor (fun _ _ => True) := by
      unfold contractDecl
      apply Parser.bind_validFor (keyword_validFor .contractKw .topItem)
      intro marker
      apply Parser.bind_validFor (identifier_validFor .topItem)
      intro name
      apply Parser.bind_validFor optionalGenericParameters_validFor
      intro genericParameters
      apply Parser.bind_validFor bodyInputs.validFor
      intro body
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    intro input inputValid
    have weakResult := weak input inputValid
    cases parsed : contractDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [parsed] at weakResult
        exact weakResult
    | ok declaration final =>
        rw [parsed] at weakResult
        have stages := parsed
        unfold contractDecl at stages
        rcases contractBind_ok_components stages with
          ⟨marker, afterMarker, markerResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨name, afterName, nameResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨parameters, afterParameters, parametersResult, rest⟩
        rcases contractBind_ok_components rest with
          ⟨body, afterBody, bodyResult, finished⟩
        have markerReply := keyword_validFor .contractKw .topItem input inputValid
        rw [markerResult] at markerReply
        have nameReply := identifier_validFor .topItem afterMarker markerReply.2.1
        rw [nameResult] at nameReply
        have parametersReply := optionalGenericParameters_validFor afterName
          nameReply.2.1
        rw [parametersResult] at parametersReply
        have bodyReply := bodyInputs.validFor afterParameters
          parametersReply.2.1
        rw [bodyResult] at bodyReply
        have markerValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerReply.1
        have nameValid : name.span.ValidFor input.file := by
          simpa only [Located.ValidFor, markerReply.2.2] using nameReply.1
        have parametersValid : Option.ValidFor
            (NonemptyDelimitedList.ValidFor Located.ValidFor) input.file
            parameters := by
          simpa [nameReply.2.2, markerReply.2.2] using parametersReply.1
        have bodyValid : ContractBody.ValidFor input.file body := by
          simpa [parametersReply.2.2, nameReply.2.2, markerReply.2.2] using
            bodyReply.1
        have markerShape := acceptToken_ok_state_shape (.keyword .contractKw)
          .topItem (· == .keyword .contractKw) markerResult
        have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
        rcases bodyInputs.startsAtCurrentTokenOnSuccess
            afterParameters body afterBody bodyResult with
          ⟨opening, openingFound, bodyStart⟩
        have openingAtAfter :=
          State.getElem?_eq_some_of_peek?_eq_some openingFound
        have openingAt : input.tokens[afterParameters.cursor]? = some opening := by
          simpa [optionalGenericParameters_preservesTokensOnSuccess afterName
              parameters afterParameters parametersResult,
            identifier_preservesTokensOnSuccess .topItem afterMarker name
              afterName nameResult,
            keyword_preservesTokensOnSuccess .contractKw .topItem input marker
              afterMarker markerResult] using openingAtAfter
        have progress : input.cursor < afterParameters.cursor :=
          Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
            (.keyword .contractKw) .topItem (· == .keyword .contractKw)
            markerResult)
            (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem
              afterMarker name afterName nameResult)
              (optionalGenericParameters_cursorMonotoneOnSuccess afterName
                parameters afterParameters parametersResult))
        have separated := inputValid.token_end_le_token_start_of_getElem?_lt
          markerAt openingAt progress
        have ordered : marker.span.startByte ≤ body.span.endByte := by
          exact Nat.le_trans markerValid.2.1 (Nat.le_trans separated (by
            rw [bodyStart]
            exact bodyValid.1.2.1))
        have outerValid := SourceSpan.cover_validFor markerValid bodyValid.1 ordered
        cases finished
        refine ⟨⟨outerValid, nameValid, ?_, ?_, bodyValid.1, bodyValid.2⟩,
          weakResult.2.1, weakResult.2.2⟩
        · cases parameters with
          | none => simp
          | some values => simpa [Option.ValidFor] using parametersValid.1
        · cases parameters with
          | none => simp
          | some values =>
              intro retained member parameter parameterMember
              have retainedEq : retained = values := by simpa using member.symm
              subst retained
              exact parametersValid.2 parameter parameterMember
  preservesTokenWindow := by
    unfold contractDecl
    apply Parser.bind_preservesTokenWindow
      (keyword_preservesTokenWindow .contractKw .topItem)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (identifier_preservesTokenWindow .topItem)
    intro name
    apply Parser.bind_preservesTokenWindow
      optionalGenericParameters_preservesTokenWindow
    intro parameters
    apply Parser.bind_preservesTokenWindow bodyInputs.preservesTokenWindow
    intro body
    exact Parser.pure_preservesTokenWindow _
  cursorMonotoneOnSuccess := by
    intro input declaration final parsed
    have stages := parsed
    unfold contractDecl at stages
    rcases contractBind_ok_components stages with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact Nat.le_trans (keyword_cursorMonotoneOnSuccess .contractKw .topItem
      input marker afterMarker markerResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem afterMarker
        name afterName nameResult)
        (Nat.le_trans (optionalGenericParameters_cursorMonotoneOnSuccess
          afterName parameters afterParameters parametersResult)
          (bodyInputs.cursorMonotoneOnSuccess afterParameters body final
            bodyResult)))
  startsAtCurrentTokenOnSuccess := by
    unfold contractDecl
    apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
      (acceptToken_startsAtCurrentTokenOnSuccess (.keyword .contractKw)
        .topItem (· == .keyword .contractKw))
    intro marker input declaration final parsed
    rcases contractBind_ok_components parsed with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    rfl
  cursorLtOnSuccess := by
    intro input final declaration parsed
    have stages := parsed
    unfold contractDecl at stages
    rcases contractBind_ok_components stages with
      ⟨marker, afterMarker, markerResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨name, afterName, nameResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨parameters, afterParameters, parametersResult, rest⟩
    rcases contractBind_ok_components rest with
      ⟨body, afterBody, bodyResult, finished⟩
    cases finished
    exact Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
      (.keyword .contractKw) .topItem (· == .keyword .contractKw) markerResult)
      (Nat.le_trans (identifier_cursorMonotoneOnSuccess .topItem afterMarker
        name afterName nameResult)
        (Nat.le_trans (optionalGenericParameters_cursorMonotoneOnSuccess
          afterName parameters afterParameters parametersResult)
          (bodyInputs.cursorMonotoneOnSuccess afterParameters body final
            bodyResult)))
}

end Solcore.Syntax.Parser.ContractInternals
