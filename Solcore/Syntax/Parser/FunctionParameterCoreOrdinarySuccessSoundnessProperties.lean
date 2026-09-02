import Solcore.Syntax.DeclarativeFunctionParameterOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Parameter

/-! Executable ordinary-success reflection for `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
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

private theorem comptimePrefixAbsent_of_core_false {input : State}
    (absent : (isContextual input .comptime &&
      match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = false) :
    DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
      input.declarativeRemainder := by
  rintro ⟨markerSpan, nameSpan, name, markerToken, nameToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.comptime.spelling
    } at markerToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := nameSpan
      value := .identifier name
    } at nameToken
  have markerPresent : isContextual input .comptime = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [markerToken.1, ↓reduceIte, markerToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have namePresent :
      (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [nameToken.1, ↓reduceIte, nameToken.2, Option.map_some]
  rw [markerPresent, namePresent] at absent
  contradiction

namespace FunctionParameterInternals

private theorem finishTypedParameter_success_shape
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) {input output : State} {value : FunctionParameter}
    (result : finishTypedParameter start marker name type input =
      .ok value output) :
    value = {
      span := SourceSpan.cover start type.span
      value := .typed marker name type
    } ∧ output.declarativeRemainder = input.declarativeRemainder := by
  unfold finishTypedParameter at result
  cases typeValue : type.value <;>
    simp only [typeValue, emitDiagnostic, modifyState, bind, pure] at result <;>
    cases result <;> simp [State.emit, State.declarativeRemainder]

private theorem errorParameter_success_shape
    (span : SourceSpan) (constraint : ParseConstraint)
    {input output : State} {value : FunctionParameter}
    (result : errorParameter span constraint input = .ok value output) :
    value = { span, value := .error } ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  unfold errorParameter at result
  simp only [emitDiagnostic, modifyState, bind, pure] at result
  cases result
  simp [State.emit, State.declarativeRemainder]

private theorem namedParameterTail_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input output : State}
    {value : FunctionParameter}
    (result : namedParameterTail start marker name errorSpan input =
      .ok value output) :
    DeclarativeGrammar.FunctionParameterTailOrdinaryParses typeOrdinary
      start marker name errorSpan input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    rcases finishTypedParameter_success_shape start marker name type finished
      with ⟨valueEq, outputEq⟩
    cases valueEq
    rw [outputEq]
    exact .typed colon.span
      (symbol_success_exactTokenParses .colon .parameter colonResult)
      (typeSuccessSound typeResult)
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    rcases errorParameter_success_shape errorSpan
      .namedParameterRequiresType result with ⟨valueEq, outputEq⟩
    cases valueEq
    rw [outputEq]
    exact .typeMissing
      (symbolAbsentAt_of_isSymbol_eq_false .colon typedFalse)

private theorem ordinaryNamedParameter_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : FunctionParameter}
    (prefixAbsent : DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
      input.declarativeRemainder)
    (result : ordinaryNamedParameter input = .ok value output) :
    DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold ordinaryNamedParameter at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  have nameParsed := identifier_success_sound .parameter nameResult
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true, emitDiagnostic, modifyState, bind] at rest
    exact .ordinary prefixAbsent nameParsed (by
      simpa [State.emit, State.declarativeRemainder] using
        namedParameterTail_success_ordinary_sound typeOrdinary
          typeSuccessSound name.span none name name.span rest)
  · have warnedFalse :
        (name.value == ContextualKeyword.comptime.spelling) = false :=
      Bool.eq_false_iff.mpr warned
    simp only [warnedFalse, Bool.false_eq_true, if_false] at rest
    exact .ordinary prefixAbsent nameParsed
      (namedParameterTail_success_ordinary_sound typeOrdinary
        typeSuccessSound name.span none name name.span rest)

private theorem comptimeNamedParameter_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : FunctionParameter}
    (result : comptimeNamedParameter input = .ok value output) :
    DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold comptimeNamedParameter at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, tailResult⟩
  exact .comptime marker.span
    (contextual_success_exactTokenParses .comptime .parameter markerResult)
    (identifier_success_sound .parameter nameResult)
    (namedParameterTail_success_ordinary_sound typeOrdinary typeSuccessSound
      marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) tailResult)

/-- Every executable Core success follows the broad function-parameter
ordinary grammar, including diagnosed missing-colon success. -/
theorem namedParameterCore_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : FunctionParameter}
    (result : namedParameterCore input = .ok value output) :
    DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold namedParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeNamedParameter_success_ordinary_sound typeOrdinary
        typeSuccessSound result
    · exact ordinaryNamedParameter_success_ordinary_sound typeOrdinary
        typeSuccessSound (comptimePrefixAbsent_of_core_false (by simp_all))
          result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryNamedParameter_success_ordinary_sound typeOrdinary
      typeSuccessSound (comptimePrefixAbsent_of_core_false (by simp_all))
        result

end FunctionParameterInternals
end Solcore.Syntax.Parser
