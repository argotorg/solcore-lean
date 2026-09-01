import Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Parameter

/-! Executable ordinary-success reflection for `lambdaParameterCore`. -/

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
    ¬ DeclarativeGrammar.ComptimeLambdaParameterStartsAt
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

namespace LambdaParameterInternals

private theorem finishTypedParameter_success_shape
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) {input output : State} {value : FunctionParameter}
    (result : FunctionParameterInternals.finishTypedParameter start marker
      name type input = .ok value output) :
    value = {
      span := SourceSpan.cover start type.span
      value := .typed marker name type
    } ∧ output.declarativeRemainder = input.declarativeRemainder := by
  unfold FunctionParameterInternals.finishTypedParameter at result
  cases typeValue : type.value <;>
    simp only [typeValue, emitDiagnostic, modifyState, bind, pure] at result <;>
    cases result <;> simp [State.emit, State.declarativeRemainder]

private theorem errorParameter_success_shape
    (span : SourceSpan) (constraint : ParseConstraint)
    {input output : State} {value : FunctionParameter}
    (result : FunctionParameterInternals.errorParameter span constraint input =
      .ok value output) :
    value = { span, value := .error } ∧
      output.declarativeRemainder = input.declarativeRemainder := by
  unfold FunctionParameterInternals.errorParameter at result
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
    (result : FunctionParameterInternals.namedParameterTail start marker name
      errorSpan input = .ok value output) :
    (∃ colonSpan afterColon type,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      typeOrdinary afterColon type output.declarativeRemainder ∧
      value = {
        span := SourceSpan.cover start type.span
        value := .typed marker name type
      }) ∨
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
        input.cursor (.symbol .colon) ∧
      value = { span := errorSpan, value := .error } ∧
      output.declarativeRemainder = input.declarativeRemainder) := by
  unfold FunctionParameterInternals.namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    rcases finishTypedParameter_success_shape start marker name type finished
      with ⟨valueEq, outputEq⟩
    left
    refine ⟨colon.span, afterColon.declarativeRemainder, type,
      symbol_success_exactTokenParses .colon .parameter colonResult, ?_,
      valueEq⟩
    rw [outputEq]
    exact typeSuccessSound typeResult
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    right
    rcases errorParameter_success_shape errorSpan
      .namedParameterRequiresType result with ⟨valueEq, outputEq⟩
    exact ⟨symbolAbsentAt_of_isSymbol_eq_false .colon typedFalse,
      valueEq, outputEq⟩

/-- Exact success of the ordinary inferred-or-typed suffix. -/
theorem ordinaryLambdaParameterTail_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (name : Identifier) {input output : State} {value : LambdaParameter}
    (result : ordinaryLambdaParameterTail name input = .ok value output) :
    DeclarativeGrammar.OrdinaryLambdaParameterTailOrdinaryParses
      typeOrdinary name input.declarativeRemainder value
        output.declarativeRemainder := by
  unfold ordinaryLambdaParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨parameter, afterParameter, tailResult, finished⟩
    cases finished
    rcases namedParameterTail_success_ordinary_sound typeOrdinary
      typeSuccessSound name.span none name name.span tailResult with
      typedResult | errorResult
    · rcases typedResult with
        ⟨colonSpan, afterColon, type, colonParsed, typeParsed, valueEq⟩
      cases valueEq
      exact .typed colonSpan colonParsed typeParsed
    · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter typed with
        ⟨colon, colonResult⟩
      exact False.elim (errorResult.1 ⟨colon.span,
        (symbol_success_exactTokenParses .colon .parameter colonResult).1⟩)
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .inferred (symbolAbsentAt_of_isSymbol_eq_false .colon typedFalse)

private theorem ordinaryLambdaParameter_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : LambdaParameter}
    (result : ordinaryLambdaParameter input = .ok value output) :
    DeclarativeGrammar.OrdinaryLambdaParameterOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold ordinaryLambdaParameter at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  have nameParsed := identifier_success_sound .parameter nameResult
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true, emitDiagnostic, modifyState, bind] at rest
    exact .parsed nameParsed (by
      simpa [State.emit, State.declarativeRemainder] using
        ordinaryLambdaParameterTail_success_ordinary_sound typeOrdinary
          typeSuccessSound name rest)
  · have warnedFalse :
        (name.value == ContextualKeyword.comptime.spelling) = false :=
      Bool.eq_false_iff.mpr warned
    simp only [warnedFalse, Bool.false_eq_true, if_false] at rest
    exact .parsed nameParsed
      (ordinaryLambdaParameterTail_success_ordinary_sound typeOrdinary
        typeSuccessSound name rest)

private theorem comptimeLambdaParameter_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : LambdaParameter}
    (result : comptimeLambdaParameter input = .ok value output) :
    DeclarativeGrammar.ComptimeLambdaParameterOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold comptimeLambdaParameter at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, tailResult⟩
  unfold comptimeLambdaParameterTail getState at tailResult
  simp only [bind] at tailResult
  by_cases typed : isSymbol afterName .colon
  · simp only [typed, if_true] at tailResult
    rcases bind_ok_components tailResult with
      ⟨parameter, afterParameter, parsedTail, finished⟩
    cases finished
    rcases namedParameterTail_success_ordinary_sound typeOrdinary
      typeSuccessSound marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) parsedTail with
      typedResult | errorResult
    · rcases typedResult with
        ⟨colonSpan, afterColon, type, colonParsed, typeParsed, valueEq⟩
      cases valueEq
      exact .typed marker.span colonSpan
        (contextual_success_exactTokenParses .comptime .parameter markerResult)
        (identifier_success_sound .parameter nameResult) colonParsed typeParsed
    · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter typed with
        ⟨colon, colonResult⟩
      exact False.elim (errorResult.1 ⟨colon.span,
        (symbol_success_exactTokenParses .colon .parameter colonResult).1⟩)
  · have typedFalse : isSymbol afterName .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at tailResult
    cases errorReply : FunctionParameterInternals.errorParameter
        (SourceSpan.cover marker.span name.span)
        .comptimeParameterRequiresType afterName with
    | invariant error => simp [errorReply] at tailResult
    | reject failure rejected => simp [errorReply] at tailResult
    | ok parameter afterError =>
        simp only [errorReply, pure] at tailResult
        cases tailResult
        rcases errorParameter_success_shape
          (SourceSpan.cover marker.span name.span)
          .comptimeParameterRequiresType errorReply with
          ⟨valueEq, outputEq⟩
        cases valueEq
        rw [outputEq]
        exact .typeMissing marker.span
          (contextual_success_exactTokenParses .comptime .parameter
            markerResult)
          (identifier_success_sound .parameter nameResult)
          (symbolAbsentAt_of_isSymbol_eq_false .colon typedFalse)

/-- Every executable Core success follows the broad ordinary grammar. -/
theorem lambdaParameterCore_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {value : LambdaParameter}
    (result : lambdaParameterCore input = .ok value output) :
    DeclarativeGrammar.LambdaParameterCoreOrdinaryParses typeOrdinary
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold lambdaParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact .comptime (comptimeLambdaParameter_success_ordinary_sound
        typeOrdinary typeSuccessSound result)
    · exact .ordinary
        (comptimePrefixAbsent_of_core_false (by simp_all))
        (ordinaryLambdaParameter_success_ordinary_sound typeOrdinary
          typeSuccessSound result)
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact .ordinary (comptimePrefixAbsent_of_core_false (by simp_all))
      (ordinaryLambdaParameter_success_ordinary_sound typeOrdinary
        typeSuccessSound result)

end LambdaParameterInternals
end Solcore.Syntax.Parser
