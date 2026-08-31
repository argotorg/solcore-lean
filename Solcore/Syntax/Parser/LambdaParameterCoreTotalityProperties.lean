import Solcore.Syntax.Parser.LambdaParameterTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
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
