import Solcore.Syntax.Parser.Internal.ParameterRecoveryTotality
import Solcore.Syntax.Parser.Internal.TypeTotality
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Parser.Internal.TypeFormTotality
import Solcore.Syntax.Parser.Internal.DelimitedSoundness

/-!
Totality of the parsers of parameters and predicates: on valid input they make progress
and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterTotalityProperties
/-! Valid-input totality and strict progress for lambda parameters. -/

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

private theorem recoverParameterAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) :
    ∀ fuel, Parser.CursorMonotoneOnSuccess
      (recoverParameterAux first last fuel) := by
  intro fuel
  induction fuel generalizing last with
  | zero => simp [recoverParameterAux, Parser.CursorMonotoneOnSuccess]
  | succ fuel inductionHypothesis =>
      intro input value final parsed
      unfold recoverParameterAux at parsed
      split at parsed
      · unfold finishRecoveredParameter at parsed
        cases parsed
        exact Nat.le_refl _
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at parsed
            unfold finishRecoveredParameter at parsed
            cases parsed
            exact Nat.le_refl _
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at parsed
            exact Nat.le_trans (by
              simp [(advance?_state_shape advanced).2])
              (inductionHypothesis token.span next value final parsed)

theorem recoverParameter_cursor_lt_onSuccess {input final : State}
    {value : FunctionParameter}
    (parsed : recoverParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold recoverParameter at parsed
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at parsed
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at parsed
      exact Nat.lt_of_lt_of_le (by
        simp [(advance?_state_shape advanced).2])
        (recoverParameterAux_cursorMonotoneOnSuccess token.span token.span
          (next.remainingCount + 1) next value final parsed)

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem recoverLambdaParameter_ordinary :
    Parser.Ordinary recoverLambdaParameter := by
  intro input
  rcases FunctionParameterInternals.recoverParameter_ordinary input with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨{ span := value.span, value := .error }, next, by
      simp [recoverLambdaParameter, result]⟩
  · exact Or.inr ⟨failure, next, by
      simp [recoverLambdaParameter, result]⟩

theorem recoverLambdaParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid recoverLambdaParameter :=
  recoverLambdaParameter_ordinary.invariantFreeOnValid

theorem recoverLambdaParameter_ne_invariant (input : State)
    (error : ParserInvariantError) :
    recoverLambdaParameter input ≠ .invariant error :=
  recoverLambdaParameter_ordinary.ne_invariant input error

theorem recoverLambdaParameter_cursor_lt_onSuccess {input final : State}
    {value : LambdaParameter}
    (parsed : recoverLambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold recoverLambdaParameter at parsed
  cases result : FunctionParameterInternals.recoverParameter input with
  | ok recovered next =>
      simp only [result] at parsed
      cases parsed
      exact FunctionParameterInternals.recoverParameter_cursor_lt_onSuccess
        result
  | reject failure next => simp [result] at parsed
  | invariant error => simp [result] at parsed

end LambdaParameterInternals

/-- Recovery discharges the public wrapper once core totality is supplied. -/
theorem lambdaParameter_invariantFreeOnValid_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore) :
    Parser.InvariantFreeOnValid lambdaParameter := by
  intro input inputValid
  rcases coreFree input inputValid with
    ⟨value, next, coreResult⟩ | ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [lambdaParameter, coreResult]⟩
  · let rewound : State := { failedState with cursor := input.cursor }
    by_cases boundary : rewound.atEnd || isSymbol rewound .comma ||
        isSymbol rewound .rightParen
    · exact Or.inr ⟨failure, rewound, by
        simp only [lambdaParameter, coreResult]
        change (if rewound.atEnd || isSymbol rewound .comma ||
            isSymbol rewound .rightParen then Reply.reject failure rewound
          else _) = _
        rw [if_pos boundary]⟩
    · rcases LambdaParameterInternals.recoverLambdaParameter_ordinary
          (rewound.emit failure.toDiagnostic) with
        ⟨value, final, recoveryResult⟩ |
        ⟨recoveryFailure, final, recoveryResult⟩
      · exact Or.inl ⟨value, final, by
          simp only [lambdaParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else LambdaParameterInternals.recoverLambdaParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩
      · exact Or.inr ⟨recoveryFailure, final, by
          simp only [lambdaParameter, coreResult]
          change (if rewound.atEnd || isSymbol rewound .comma ||
              isSymbol rewound .rightParen then _
            else LambdaParameterInternals.recoverLambdaParameter
              (rewound.emit failure.toDiagnostic)) = _
          rw [if_neg boundary, recoveryResult]⟩

theorem lambdaParameter_ne_invariant_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    lambdaParameter input ≠ .invariant error :=
  (lambdaParameter_invariantFreeOnValid_of_core coreFree).ne_invariant
    input inputValid error

theorem lambdaParameter_cursor_lt_onSuccess_of_core
    (coreStrict : ∀ {input final : State} {value : LambdaParameter},
      LambdaParameterInternals.lambdaParameterCore input = .ok value final →
        input.cursor < final.cursor)
    {input final : State} {value : LambdaParameter}
    (parsed : lambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold lambdaParameter at parsed
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok coreValue next =>
      simp only [coreResult] at parsed
      cases parsed
      exact coreStrict coreResult
  | invariant error => simp [coreResult] at parsed
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok value final at parsed
      split at parsed
      · contradiction
      · simpa [rewound, State.emit] using
          LambdaParameterInternals.recoverLambdaParameter_cursor_lt_onSuccess
            parsed

/-- Conditional full contract; only the non-recovering core remains. -/
theorem lambdaParameter_elementTotalityContract_of_core
    (coreFree : Parser.InvariantFreeOnValid
      LambdaParameterInternals.lambdaParameterCore)
    (coreStrict : ∀ {input final : State} {value : LambdaParameter},
      LambdaParameterInternals.lambdaParameterCore input = .ok value final →
        input.cursor < final.cursor) :
    ElementTotalityContract lambdaParameter := {
  validFor := lambdaParameter_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := lambdaParameter_preservesTokenWindow
  cursorLtOnSuccess := lambdaParameter_cursor_lt_onSuccess_of_core coreStrict
  invariantFree := lambdaParameter_ne_invariant_of_core coreFree
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterCoreTotalityProperties
/-! Totality and strict progress for the non-recovering lambda parameter core. -/
set_option autoImplicit false
namespace Solcore.Syntax.Parser
namespace LambdaParameterInternals
private theorem map_invariantFreeOnValid {alpha beta : Type}
    (parser : Parser alpha) (map : alpha → beta)
    (free : Parser.InvariantFreeOnValid parser) :
    Parser.InvariantFreeOnValid (do pure (map (← parser))) := by
  intro input inputValid
  rcases free input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩
  · exact Or.inl ⟨map value, next, by
      simp only [bind, result, pure]⟩
  · exact Or.inr ⟨failure, next, by
      simp only [bind, result]⟩
private theorem finishTypedParameter_ordinary (start : SourceSpan)
    (marker : Option SourceSpan) (name : Identifier) (type : TypeExpr) :
    Parser.Ordinary (FunctionParameterInternals.finishTypedParameter
      start marker name type) := by
  intro input
  unfold FunctionParameterInternals.finishTypedParameter
  cases type.value <;> exact Or.inl ⟨_, _, rfl⟩
private theorem errorParameter_ordinary (span : SourceSpan)
    (constraint : ParseConstraint) :
    Parser.Ordinary
      (FunctionParameterInternals.errorParameter span constraint) := by
  intro input
  unfold FunctionParameterInternals.errorParameter
  exact Or.inl ⟨_, _, rfl⟩
private theorem namedParameterTail_invariantFreeOnValid
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) : Parser.InvariantFreeOnValid
      (FunctionParameterInternals.namedParameterTail start marker name
        errorSpan) := by
  unfold FunctionParameterInternals.namedParameterTail
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
    exact (finishTypedParameter_ordinary start marker name type).invariantFreeOnValid
  · simp only [typed, Bool.false_eq_true, if_false]
    exact (errorParameter_ordinary errorSpan
      .namedParameterRequiresType).invariantFreeOnValid
private theorem ordinaryLambdaParameterTail_invariantFreeOnValid
    (name : Identifier) :
    Parser.InvariantFreeOnValid (ordinaryLambdaParameterTail name) := by
  unfold ordinaryLambdaParameterTail
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    exact map_invariantFreeOnValid _ ofFunctionParameter
      (namedParameterTail_invariantFreeOnValid name.span none name name.span)
  · simp only [typed, Bool.false_eq_true, if_false]
    exact Parser.pure_invariantFreeOnValid
      ({ span := name.span, value := .inferred name } : LambdaParameter)
private theorem comptimeLambdaParameterTail_invariantFreeOnValid
    (marker : Token) (name : Identifier) :
    Parser.InvariantFreeOnValid (comptimeLambdaParameterTail marker name) := by
  unfold comptimeLambdaParameterTail
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    exact map_invariantFreeOnValid _ ofFunctionParameter
      (namedParameterTail_invariantFreeOnValid marker.span
        (some marker.span) name (SourceSpan.cover marker.span name.span))
  · simp only [typed, Bool.false_eq_true, if_false]
    exact map_invariantFreeOnValid _ ofFunctionParameter
      (errorParameter_ordinary (SourceSpan.cover marker.span name.span)
        .comptimeParameterRequiresType).invariantFreeOnValid
private theorem ordinaryLambdaParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid ordinaryLambdaParameter := by
  intro input inputValid
  rcases (identifier_ordinary .parameter) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameReply := identifier_validFor .parameter input inputValid
    rw [nameResult] at nameReply
    have nameValid : name.span.ValidFor afterName.file := by
      simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
    by_cases warned : name.value == ContextualKeyword.comptime.spelling
    · let diagnostic : ParseDiagnostic := {
        span := name.span
        kind := .constraintViolation .comptimeUsedAsParameterName
      }
      have emittedValid := nameReply.2.1.emit_validFor diagnostic nameValid
      rcases ordinaryLambdaParameterTail_invariantFreeOnValid name
          (afterName.emit diagnostic) emittedValid with
        ⟨value, final, result⟩ | ⟨failure, final, result⟩
      · exact Or.inl ⟨value, final, by
          simp only [ordinaryLambdaParameter, bind, nameResult, warned,
            ↓reduceIte, emitDiagnostic, modifyState, diagnostic, result]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [ordinaryLambdaParameter, bind, nameResult, warned,
            ↓reduceIte, emitDiagnostic, modifyState, diagnostic, result]⟩
    · rcases ordinaryLambdaParameterTail_invariantFreeOnValid name afterName
          nameReply.2.1 with
        ⟨value, final, result⟩ | ⟨failure, final, result⟩
      · exact Or.inl ⟨value, final, by
          simp only [ordinaryLambdaParameter, bind, nameResult, warned,
            Bool.false_eq_true, ↓reduceIte, result]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [ordinaryLambdaParameter, bind, nameResult, warned,
            Bool.false_eq_true, ↓reduceIte, result]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [ordinaryLambdaParameter, bind, nameResult]⟩
private theorem comptimeLambdaParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid comptimeLambdaParameter := by
  unfold comptimeLambdaParameter
  apply Parser.bind_invariantFreeOnValid
    (contextual_validFor .comptime .parameter)
    (contextual_ordinary .comptime .parameter).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid (identifier_validFor .parameter)
    (identifier_ordinary .parameter).invariantFreeOnValid
  intro name
  exact comptimeLambdaParameterTail_invariantFreeOnValid marker name
theorem lambdaParameterCore_invariantFreeOnValid :
    Parser.InvariantFreeOnValid lambdaParameterCore := by
  intro input inputValid
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_invariantFreeOnValid input inputValid
    · exact ordinaryLambdaParameter_invariantFreeOnValid input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameter_invariantFreeOnValid input inputValid
private theorem ordinaryLambdaParameterTail_cursorMonotoneOnSuccess
    (name : Identifier) :
    Parser.CursorMonotoneOnSuccess (ordinaryLambdaParameterTail name) := by
  intro input value final parsed
  unfold ordinaryLambdaParameterTail getState at parsed
  simp only [bind] at parsed
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at parsed
    cases result : FunctionParameterInternals.namedParameterTail
        name.span none name name.span input with
    | ok parameter next =>
        simp only [result, pure] at parsed
        cases parsed
        exact (FunctionParameterInternals.namedParameterTail_ok_state_shape
          name.span none name name.span rfl result).1
    | reject failure next => simp [result] at parsed
    | invariant error => simp [result] at parsed
  · simp only [typed, Bool.false_eq_true, if_false, pure] at parsed
    cases parsed
    exact Nat.le_refl _
private theorem comptimeLambdaParameterTail_cursorMonotoneOnSuccess
    (marker : Token) (name : Identifier) :
    Parser.CursorMonotoneOnSuccess
      (comptimeLambdaParameterTail marker name) := by
  intro input value final parsed
  unfold comptimeLambdaParameterTail getState at parsed
  simp only [bind] at parsed
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at parsed
    cases result : FunctionParameterInternals.namedParameterTail marker.span
        (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | ok parameter next =>
        simp only [result, pure] at parsed
        cases parsed
        exact (FunctionParameterInternals.namedParameterTail_ok_state_shape
          marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span) rfl result).1
    | reject failure next => simp [result] at parsed
    | invariant error => simp [result] at parsed
  · simp only [typed] at parsed
    cases result : FunctionParameterInternals.errorParameter
        (SourceSpan.cover marker.span name.span)
        .comptimeParameterRequiresType input with
    | ok parameter next =>
        simp only [pure] at parsed
        cases parsed
        simp [State.emit]
    | reject failure next => simp [result] at parsed
    | invariant error => simp [result] at parsed
private theorem ordinaryLambdaParameter_cursor_lt_onSuccess
    {input final : State} {value : LambdaParameter}
    (parsed : ordinaryLambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold ordinaryLambdaParameter at parsed
  simp only [bind] at parsed
  cases nameResult : identifier .parameter input with
  | ok name afterName =>
      simp only [nameResult] at parsed
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        simp only [warned, if_true, emitDiagnostic, modifyState] at parsed
        have tailMonotone :=
          ordinaryLambdaParameterTail_cursorMonotoneOnSuccess name
            (afterName.emit diagnostic) value final (by
              simpa [diagnostic] using parsed)
        exact Nat.lt_of_lt_of_le
          ((identifier_elementTotalityContract .parameter).cursorLtOnSuccess
            nameResult)
          (by simpa [State.emit] using tailMonotone)
      · have absent : (name.value == ContextualKeyword.comptime.spelling) =
            false := by
          cases found : name.value == ContextualKeyword.comptime.spelling with
          | false => rfl
          | true => exact False.elim (warned found)
        simp only [absent, Bool.false_eq_true, if_false] at parsed
        exact Nat.lt_of_lt_of_le
          ((identifier_elementTotalityContract .parameter).cursorLtOnSuccess
            nameResult)
          (ordinaryLambdaParameterTail_cursorMonotoneOnSuccess name afterName
            value final parsed)
  | reject failure next => simp [nameResult] at parsed
  | invariant error => simp [nameResult] at parsed
private theorem comptimeLambdaParameter_cursor_lt_onSuccess
    {input final : State} {value : LambdaParameter}
    (parsed : comptimeLambdaParameter input = .ok value final) :
    input.cursor < final.cursor := by
  unfold comptimeLambdaParameter at parsed
  simp only [bind] at parsed
  cases markerResult : contextual .comptime .parameter input with
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases nameResult : identifier .parameter afterMarker with
      | ok name afterName =>
          simp only [nameResult] at parsed
          exact Nat.lt_of_lt_of_le
            ((contextual_elementTotalityContract .comptime .parameter).cursorLtOnSuccess
              markerResult)
            (Nat.le_trans
              (Nat.le_of_lt
                ((identifier_elementTotalityContract .parameter).cursorLtOnSuccess
                  nameResult))
              (comptimeLambdaParameterTail_cursorMonotoneOnSuccess marker name
                afterName value final parsed))
      | reject failure next => simp [nameResult] at parsed
      | invariant error => simp [nameResult] at parsed
  | reject failure next => simp [markerResult] at parsed
  | invariant error => simp [markerResult] at parsed
theorem lambdaParameterCore_cursor_lt_onSuccess {input final : State}
    {value : LambdaParameter}
    (parsed : lambdaParameterCore input = .ok value final) :
    input.cursor < final.cursor := by
  unfold lambdaParameterCore at parsed
  split at parsed
  · simp only [Bool.and_true] at parsed
    split at parsed
    · exact comptimeLambdaParameter_cursor_lt_onSuccess parsed
    · exact ordinaryLambdaParameter_cursor_lt_onSuccess parsed
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at parsed
    exact ordinaryLambdaParameter_cursor_lt_onSuccess parsed
end LambdaParameterInternals
theorem lambdaParameter_invariantFreeOnValid :
    Parser.InvariantFreeOnValid lambdaParameter :=
  lambdaParameter_invariantFreeOnValid_of_core
    LambdaParameterInternals.lambdaParameterCore_invariantFreeOnValid
theorem lambdaParameter_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    lambdaParameter input ≠ .invariant error :=
  lambdaParameter_invariantFreeOnValid.ne_invariant input inputValid error
theorem lambdaParameter_cursor_lt_onSuccess {input final : State}
    {value : LambdaParameter}
    (parsed : lambdaParameter input = .ok value final) :
    input.cursor < final.cursor :=
  lambdaParameter_cursor_lt_onSuccess_of_core
    LambdaParameterInternals.lambdaParameterCore_cursor_lt_onSuccess parsed
theorem lambdaParameter_elementTotalityContract :
    ElementTotalityContract lambdaParameter :=
  lambdaParameter_elementTotalityContract_of_core
    LambdaParameterInternals.lambdaParameterCore_invariantFreeOnValid
    LambdaParameterInternals.lambdaParameterCore_cursor_lt_onSuccess
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterTotalityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateTotalityProperties
/-! Valid-input totality for one canonical trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every production stage of a trait predicate has an ordinary outcome. -/
theorem predicate_invariantFreeOnValid :
    Parser.InvariantFreeOnValid predicate := by
  unfold predicate
  apply Parser.bind_invariantFreeOnValid typeExpr_validFor
    typeExpr_invariantFreeOnValid
  intro subject
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .colon .typeExpr)
    (symbol_ordinary .colon .typeExpr).invariantFreeOnValid
  intro _colon
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .typeExpr)
    (identifier_ordinary .typeExpr).invariantFreeOnValid
  intro traitName
  apply Parser.bind_invariantFreeOnValid
    (parseNamedTypeArguments_validFor typeExpr typeExpr_validFor
      typeExpr_preservesTokensOnSuccess)
    (fun input inputValid => parseNamedTypeArguments_ordinary typeExpr
      typeExpr_elementTotalityContract input inputValid)
  intro arguments
  let endSpan := match arguments with
    | some values => values.span
    | none => traitName.span
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover subject.span endSpan
    subject
    traitName
    arguments
  } : Predicate)

theorem predicate_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    predicate input ≠ .invariant error :=
  predicate_invariantFreeOnValid.ne_invariant input inputValid error

/-- Predicate syntax/state laws paired with unconditional totality. -/
theorem predicate_elementTotalityContract :
    ElementTotalityContract predicate := {
  validFor := predicate_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := predicate_preservesTokenWindow
  cursorLtOnSuccess := PredicateInternals.predicate_cursor_lt_onSuccess
  invariantFree := predicate_ne_invariant
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceTotalityProperties
/-! Valid-input totality for canonical predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One canonical predicate has only ordinary outcomes on valid inputs. -/
theorem predicate_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ value next, predicate input = .ok value next) ∨
      (∃ failure next, predicate input = .reject failure next) :=
  predicate_invariantFreeOnValid input inputValid

namespace PredicateInternals

private theorem remainingCount_lt_after_strict_progress
    {input next : State} {fuel : Nat}
    (nextValid : next.ValidFor) (windowEq : next.window = input.window)
    (progress : input.cursor < next.cursor)
    (adequate : input.remainingCount < fuel + 1) :
    next.remainingCount < fuel := by
  have nextCursorBound : next.cursor ≤ input.window.endIndex := by
    simpa [windowEq] using nextValid.cursor_le_endIndex
  have endIndexEq : next.window.endIndex = input.window.endIndex :=
    congrArg TokenWindow.endIndex windowEq
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq]
  omega

/-- More fuel than remaining tokens makes the bare-sequence loop ordinary. -/
theorem barePredicatesTail_ordinary_of_remainingCount_lt
    (first : Predicate) : ∀ fuel last tailRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ values next,
        barePredicatesTail first fuel last tailRev input = .ok values next) ∨
      (∃ failure next,
        barePredicatesTail first fuel last tailRev input =
          .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev input inputValid adequate
      unfold barePredicatesTail
      split
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .typeExpr input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .typeExpr input inputValid
            rw [commaResult] at commaReply
            simp only
            split
            · cases valueResult : predicate afterComma with
              | invariant error =>
                  exact False.elim
                    (predicate_ne_invariant afterComma commaReply.2.1 error
                      valueResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok value next =>
                  change
                    (∃ values final,
                      barePredicatesTail first fuel value
                        (value :: tailRev) next = .ok values final) ∨
                    (∃ failure final,
                      barePredicatesTail first fuel value
                        (value :: tailRev) next = .reject failure final)
                  apply inductionHypothesis value (value :: tailRev) next
                  · have valueReply := predicate_validFor afterComma
                      commaReply.2.1
                    rw [valueResult] at valueReply
                    exact valueReply.2.1
                  · have valueReply := predicate_validFor afterComma
                      commaReply.2.1
                    rw [valueResult] at valueReply
                    have commaWindow := symbol_preservesTokenWindow .comma
                      .typeExpr input
                    rw [commaResult] at commaWindow
                    have valueWindow := predicate_preservesTokenWindow afterComma
                    rw [valueResult] at valueWindow
                    exact remainingCount_lt_after_strict_progress valueReply.2.1
                      (valueWindow.2.trans commaWindow.2)
                      (Nat.lt_trans
                        (acceptToken_cursor_lt_onSuccess (.symbol .comma)
                          .typeExpr (· == .symbol .comma) commaResult)
                        (predicate_cursor_lt_onSuccess valueResult)) adequate
            · exact Or.inl ⟨_, _, rfl⟩
      · exact Or.inl ⟨_, _, rfl⟩

theorem barePredicatesTail_ne_invariant_of_remainingCount_lt
    (first last : Predicate) (fuel : Nat) (tailRev : List Predicate)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    barePredicatesTail first fuel last tailRev input ≠ .invariant error := by
  intro failed
  rcases barePredicatesTail_ordinary_of_remainingCount_lt first fuel last
      tailRev input inputValid adequate with
    ⟨values, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production fuel selected by `barePredicates` is always adequate. -/
theorem barePredicatesTail_production_ordinary (first last : Predicate)
    (tailRev : List Predicate) (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next,
      barePredicatesTail first (input.remainingCount + 1) last tailRev input =
        .ok values next) ∨
    (∃ failure next,
      barePredicatesTail first (input.remainingCount + 1) last tailRev input =
        .reject failure next) :=
  barePredicatesTail_ordinary_of_remainingCount_lt first
    (input.remainingCount + 1) last tailRev input inputValid (by omega)

/-- Bare predicate sequences have only ordinary outcomes on valid inputs. -/
theorem barePredicates_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, barePredicates input = .ok values next) ∨
      (∃ failure next, barePredicates input = .reject failure next) := by
  unfold barePredicates
  cases firstResult : predicate input with
  | invariant error =>
      exact False.elim
        (predicate_ne_invariant input inputValid error firstResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      have firstReply := predicate_validFor input inputValid
      rw [firstResult] at firstReply
      exact barePredicatesTail_production_ordinary first first [] next
        firstReply.2.1

theorem barePredicates_invariantFreeOnValid :
    Parser.InvariantFreeOnValid barePredicates :=
  barePredicates_ordinary

theorem barePredicates_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    barePredicates input ≠ .invariant error :=
  barePredicates_invariantFreeOnValid.ne_invariant input inputValid error

/-- Parenthesized predicate sequences discharge their nonempty refinement. -/
theorem groupedPredicates_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, groupedPredicates input = .ok values next) ∨
      (∃ failure next, groupedPredicates input = .reject failure next) := by
  rcases delimited_ordinary .leftParen .rightParen false predicate .typeExpr
      .topLevel predicate_elementTotalityContract input inputValid with
    ⟨values, afterValues, valuesResult⟩ |
    ⟨failure, rejected, valuesResult⟩
  · have nonempty := delimited_false_elements_ne_nil_onSuccess .leftParen
      .rightParen predicate .typeExpr .topLevel valuesResult
    cases elements : values.elements with
    | nil => exact False.elim (nonempty elements)
    | cons head tail =>
        exact Or.inl ⟨{
          span := values.span
          elements := { head, tail }
        }, afterValues, by
          simp only [groupedPredicates, bind, valuesResult, elements, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [groupedPredicates, bind, valuesResult]⟩

theorem groupedPredicates_invariantFreeOnValid :
    Parser.InvariantFreeOnValid groupedPredicates :=
  groupedPredicates_ordinary

theorem groupedPredicates_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    groupedPredicates input ≠ .invariant error :=
  groupedPredicates_invariantFreeOnValid.ne_invariant input inputValid error

/-- Predicate-sequence dispatch is ordinary in both grouped and bare forms. -/
theorem predicateSequence_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ values next, predicateSequence input = .ok values next) ∨
      (∃ failure next, predicateSequence input = .reject failure next) := by
  unfold predicateSequence
  split
  · exact Parser.orElse_invariantFreeOnValid
      groupedPredicates_invariantFreeOnValid
      barePredicates_invariantFreeOnValid input inputValid
  · exact barePredicates_ordinary input inputValid

theorem predicateSequence_invariantFreeOnValid :
    Parser.InvariantFreeOnValid predicateSequence :=
  predicateSequence_ordinary

theorem predicateSequence_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    predicateSequence input ≠ .invariant error :=
  predicateSequence_invariantFreeOnValid.ne_invariant input inputValid error

end PredicateInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WhereClauseTotalityProperties
/-! Valid-input totality for canonical optional `where` clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `where` parsing is ordinary in both present and absent paths. -/
theorem whereClause_invariantFreeOnValid :
    Parser.InvariantFreeOnValid whereClause := by
  unfold whereClause
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isContextual observed .where
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (contextual_validFor .where .typeExpr)
      (contextual_ordinary .where .typeExpr).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid
      PredicateInternals.predicateSequence_validFor
      PredicateInternals.predicateSequence_invariantFreeOnValid
    intro predicates
    exact Parser.pure_invariantFreeOnValid (some ({
      span := SourceSpan.cover marker.span predicates.span
      predicates := predicates.elements
    } : WhereClause))
  · simp only [present, Bool.false_eq_true, if_false]
    exact Parser.pure_invariantFreeOnValid none

theorem whereClause_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ clause next, whereClause input = .ok clause next) ∨
      (∃ failure next, whereClause input = .reject failure next) :=
  whereClause_invariantFreeOnValid input inputValid

theorem whereClause_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    whereClause input ≠ .invariant error :=
  whereClause_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end
