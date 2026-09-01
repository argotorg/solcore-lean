import Solcore.Syntax.Parser.LambdaParameterTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Valid-input totality and strict progress for named function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FunctionParameterInternals

private theorem finishTypedParameter_ordinary (start : SourceSpan)
    (marker : Option SourceSpan) (name : Identifier) (type : TypeExpr) :
    Parser.Ordinary (finishTypedParameter start marker name type) := by
  intro input
  unfold finishTypedParameter
  cases type.value <;> exact Or.inl ⟨_, _, rfl⟩

private theorem errorParameter_ordinary (span : SourceSpan)
    (constraint : ParseConstraint) :
    Parser.Ordinary (errorParameter span constraint) := by
  intro input
  exact Or.inl ⟨_, _, by unfold errorParameter; rfl⟩

private theorem namedParameterTail_invariantFreeOnValid
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) :
    Parser.InvariantFreeOnValid
      (namedParameterTail start marker name errorSpan) := by
  unfold namedParameterTail
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .colon .parameter)
      (symbol_ordinary .colon .parameter).invariantFreeOnValid
    intro colon
    apply Parser.bind_invariantFreeOnValid typeExpr_validFor
      typeExpr_invariantFreeOnValid
    intro type
    exact (finishTypedParameter_ordinary start marker name type
      ).invariantFreeOnValid
  · simp only [typed, Bool.false_eq_true, if_false]
    exact (errorParameter_ordinary errorSpan
      .namedParameterRequiresType).invariantFreeOnValid

private theorem ordinaryNamedParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid ordinaryNamedParameter := by
  intro input inputValid
  rcases (identifier_ordinary .parameter) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameReply := identifier_validFor .parameter input inputValid
    rw [nameResult] at nameReply
    by_cases warned : name.value == ContextualKeyword.comptime.spelling
    · let diagnostic : ParseDiagnostic := {
        span := name.span
        kind := .constraintViolation .comptimeUsedAsParameterName
      }
      have nameSpanValid : name.span.ValidFor afterName.file := by
        simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
      have emittedValid := nameReply.2.1.emit_validFor diagnostic nameSpanValid
      rcases namedParameterTail_invariantFreeOnValid name.span none name
          name.span (afterName.emit diagnostic) emittedValid with
        ⟨value, final, result⟩ | ⟨failure, final, result⟩
      · exact Or.inl ⟨value, final, by
          simp only [ordinaryNamedParameter, bind, nameResult, warned,
            ↓reduceIte, emitDiagnostic, modifyState, diagnostic, result]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [ordinaryNamedParameter, bind, nameResult, warned,
            ↓reduceIte, emitDiagnostic, modifyState, diagnostic, result]⟩
    · rcases namedParameterTail_invariantFreeOnValid name.span none name
          name.span afterName nameReply.2.1 with
        ⟨value, final, result⟩ | ⟨failure, final, result⟩
      · exact Or.inl ⟨value, final, by
          simp only [ordinaryNamedParameter, bind, nameResult, warned,
            Bool.false_eq_true, ↓reduceIte, result]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [ordinaryNamedParameter, bind, nameResult, warned,
            Bool.false_eq_true, ↓reduceIte, result]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [ordinaryNamedParameter, bind, nameResult]⟩

private theorem comptimeNamedParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .comptime .parameter)
    (contextual_ordinary .comptime .parameter).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid (identifier_validFor .parameter)
    (identifier_ordinary .parameter).invariantFreeOnValid
  intro name
  exact namedParameterTail_invariantFreeOnValid marker.span
    (some marker.span) name (SourceSpan.cover marker.span name.span)

theorem namedParameterCore_invariantFreeOnValid :
    Parser.InvariantFreeOnValid namedParameterCore := by
  intro input inputValid
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_invariantFreeOnValid input inputValid
    · exact ordinaryNamedParameter_invariantFreeOnValid input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_invariantFreeOnValid input inputValid

private theorem ordinaryNamedParameter_cursor_lt_onSuccess
    {input final : State} {value : FunctionParameter}
    (parsed : ordinaryNamedParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold ordinaryNamedParameter at parsed
  simp only [bind] at parsed
  cases nameResult : identifier .parameter input with
  | reject failure next => simp [nameResult] at parsed
  | invariant error => simp [nameResult] at parsed
  | ok name afterName =>
      simp only [nameResult] at parsed
      have nameStrict :=
        (identifier_elementTotalityContract .parameter).cursorLtOnSuccess
          nameResult
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        simp only [warned, if_true, emitDiagnostic, modifyState] at parsed
        have tail := namedParameterTail_ok_state_shape name.span none name
          name.span rfl (by simpa [diagnostic] using parsed)
        exact Nat.lt_of_lt_of_le nameStrict (by
          simpa [State.emit] using tail.1)
      · have absent : (name.value == ContextualKeyword.comptime.spelling) =
            false := by
          cases found : name.value == ContextualKeyword.comptime.spelling with
          | false => rfl
          | true => exact False.elim (warned found)
        simp only [absent, Bool.false_eq_true, if_false] at parsed
        exact Nat.lt_of_lt_of_le nameStrict
          (namedParameterTail_ok_state_shape name.span none name name.span rfl
            parsed).1

private theorem comptimeNamedParameter_cursor_lt_onSuccess
    {input final : State} {value : FunctionParameter}
    (parsed : comptimeNamedParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold comptimeNamedParameter at parsed
  simp only [bind] at parsed
  cases markerResult : contextual .comptime .parameter input with
  | reject failure next => simp [markerResult] at parsed
  | invariant error => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases nameResult : identifier .parameter afterMarker with
      | reject failure next => simp [nameResult] at parsed
      | invariant error => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          exact Nat.lt_of_lt_of_le
            ((contextual_elementTotalityContract .comptime .parameter
              ).cursorLtOnSuccess markerResult)
            (Nat.le_trans
              (identifier_cursorMonotoneOnSuccess .parameter afterMarker name
                afterName nameResult)
              (namedParameterTail_ok_state_shape marker.span
                (some marker.span) name (SourceSpan.cover marker.span name.span)
                rfl parsed).1)

theorem namedParameterCore_cursor_lt_onSuccess
    {input final : State} {value : FunctionParameter}
    (parsed : namedParameterCore input = .ok value final) :
    input.cursor < final.cursor := by
  unfold namedParameterCore at parsed
  split at parsed
  · simp only [Bool.and_true] at parsed
    split at parsed
    · exact comptimeNamedParameter_cursor_lt_onSuccess parsed
    · exact ordinaryNamedParameter_cursor_lt_onSuccess parsed
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at parsed
    exact ordinaryNamedParameter_cursor_lt_onSuccess parsed

end FunctionParameterInternals

/-- Core parsing or recovery gives every named parameter an ordinary result. -/
theorem namedParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid namedParameter := by
  intro input inputValid
  rcases FunctionParameterInternals.namedParameterCore_invariantFreeOnValid
      input inputValid with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by simp only [namedParameter, coreResult]⟩
  · let rewound : State := { failedState with cursor := input.cursor }
    by_cases boundary : rewound.atEnd || isSymbol rewound .comma ||
        isSymbol rewound .rightParen
    · exact Or.inr ⟨failure, rewound, by
        simp only [namedParameter, coreResult]
        change (if rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen then Reply.reject failure rewound
          else _) = _
        rw [if_pos boundary]⟩
    · rcases FunctionParameterInternals.recoverParameter_ordinary
          (rewound.emit failure.toDiagnostic) with
        ⟨value, final, recoveryResult⟩ |
        ⟨recoveryFailure, final, recoveryResult⟩
      · exact Or.inl ⟨value, final, by
          simp only [namedParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else FunctionParameterInternals.recoverParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, final, by
          simp only [namedParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else FunctionParameterInternals.recoverParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩

theorem namedParameter_ordinary
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, namedParameter input = .ok value next) ∨
      (∃ failure next, namedParameter input = .reject failure next) :=
  namedParameter_invariantFreeOnValid input inputValid

theorem namedParameter_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    namedParameter input ≠ .invariant error :=
  namedParameter_invariantFreeOnValid.ne_invariant input inputValid error

theorem namedParameter_cursor_lt_onSuccess
    {input final : State} {value : FunctionParameter}
    (parsed : namedParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold namedParameter at parsed
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | invariant error => simp [coreResult] at parsed
  | ok coreValue next =>
      simp only [coreResult] at parsed
      cases parsed
      exact FunctionParameterInternals.namedParameterCore_cursor_lt_onSuccess
        coreResult
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) = .ok value final at parsed
      split at parsed
      · contradiction
      · simpa [rewound, State.emit] using
          FunctionParameterInternals.recoverParameter_cursor_lt_onSuccess parsed

theorem namedParameter_elementTotalityContract :
    ElementTotalityContract namedParameter := {
  validFor := namedParameter_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := namedParameter_preservesTokenWindow
  cursorLtOnSuccess := namedParameter_cursor_lt_onSuccess
  invariantFree := namedParameter_ne_invariant
}

end Solcore.Syntax.Parser
