import Solcore.Syntax.Parser.ParameterRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.ParameterProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Diagnostic-free success soundness for named function parameters. -/

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

private theorem comptimeParameterPrefixAbsentAt_of_core_false
    {input : State}
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

private theorem namedParameterTail_success_sound
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input next : State} {value : FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.namedParameterTail
      start marker name errorSpan input = .ok value next) :
    ∃ colonSpan afterColon type,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      DeclarativeGrammar.TypeExprParses afterColon type
        next.declarativeRemainder ∧
      value = {
        span := SourceSpan.cover start type.span
        value := .typed marker name type
      } := by
  unfold FunctionParameterInternals.namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    have typeGrammar := typeExpr_success_sound typeResult
    unfold FunctionParameterInternals.finishTypedParameter at finished
    cases typeValue : type.value <;>
      simp only [typeValue, emitDiagnostic, modifyState, bind, pure]
        at finished <;>
      cases finished
    all_goals
      refine ⟨colon.span, afterColon.declarativeRemainder, type,
        symbol_success_exactTokenParses .colon .parameter colonResult, ?_, rfl⟩
      simpa only [State.declarativeRemainder, State.emit] using typeGrammar
  · simp only [typed, Bool.false_eq_true, if_false] at result
    exact False.elim
      (FunctionParameterInternals.errorParameter_diagnostics_ne_nil_onSuccess
        errorSpan .namedParameterRequiresType result diagnosticFree)

private theorem ordinaryNamedParameter_success_sound
    {input next : State} {value : FunctionParameter}
    (prefixAbsent :
      DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
        input.declarativeRemainder)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.ordinaryNamedParameter input =
      .ok value next) :
    DeclarativeGrammar.FunctionParameterParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold FunctionParameterInternals.ordinaryNamedParameter at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  have nameGrammar := identifier_success_sound .parameter nameResult
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true, emitDiagnostic, modifyState, bind] at rest
    rcases namedParameterTail_success_sound name.span none name name.span
        diagnosticFree rest with
      ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, valueEq⟩
    subst value
    exact .ordinary colonSpan prefixAbsent nameGrammar
      (by simpa only [State.declarativeRemainder, State.emit]
        using colonGrammar)
      typeGrammar
  · have warnedFalse :
        (name.value == ContextualKeyword.comptime.spelling) = false :=
      Bool.eq_false_iff.mpr warned
    simp only [warnedFalse, Bool.false_eq_true, if_false] at rest
    rcases namedParameterTail_success_sound name.span none name name.span
        diagnosticFree rest with
      ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, valueEq⟩
    subst value
    exact .ordinary colonSpan prefixAbsent nameGrammar colonGrammar typeGrammar

private theorem comptimeNamedParameter_success_sound
    {input next : State} {value : FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.comptimeNamedParameter input =
      .ok value next) :
    DeclarativeGrammar.FunctionParameterParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold FunctionParameterInternals.comptimeNamedParameter at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, tailResult⟩
  rcases namedParameterTail_success_sound marker.span (some marker.span) name
      (SourceSpan.cover marker.span name.span) diagnosticFree tailResult with
    ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, valueEq⟩
  subst value
  exact .comptime marker.span colonSpan
    (contextual_success_exactTokenParses .comptime .parameter markerResult)
    (identifier_success_sound .parameter nameResult) colonGrammar typeGrammar

private theorem namedParameterCore_success_sound
    {input next : State} {value : FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.namedParameterCore input =
      .ok value next) :
    DeclarativeGrammar.FunctionParameterParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold FunctionParameterInternals.namedParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeNamedParameter_success_sound diagnosticFree result
    · exact ordinaryNamedParameter_success_sound
        (comptimeParameterPrefixAbsentAt_of_core_false (by simp_all))
        diagnosticFree result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryNamedParameter_success_sound
      (comptimeParameterPrefixAbsentAt_of_core_false (by simp_all))
      diagnosticFree result

/-- Every diagnostic-free named-parameter success follows the strict grammar. -/
theorem namedParameter_success_sound {input next : State}
    {value : FunctionParameter} (diagnosticFree : next.diagnosticsRev = [])
    (result : namedParameter input = .ok value next) :
    DeclarativeGrammar.FunctionParameterParses input.declarativeRemainder
      value next.declarativeRemainder := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact namedParameterCore_success_sound diagnosticFree coreResult
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (FunctionParameterInternals.recoverParameter_diagnostics_ne_nil_onSuccess
            result diagnosticFree)
  | invariant error => simp [coreResult] at result

/-- Strict parameter grammar soundness composes with source validity. -/
theorem namedParameter_success_sound_and_validFor {input next : State}
    {value : FunctionParameter} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : namedParameter input = .ok value next) :
    DeclarativeGrammar.FunctionParameterParses input.declarativeRemainder
        value next.declarativeRemainder ∧
      FunctionParameter.ValidFor input.file value := by
  refine ⟨namedParameter_success_sound diagnosticFree result, ?_⟩
  have valid := namedParameter_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
