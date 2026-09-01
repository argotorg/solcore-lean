import Solcore.Syntax.Parser.Parameter

/-! Diagnostic commitments of named-parameter errors and recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {α β : Type} {first : Parser α}
    {next : α → Parser β} {input final : State} {value : β}
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
  | reject failure rejected =>
      rw [firstResult] at parsed
      contradiction
  | invariant error =>
      rw [firstResult] at parsed
      contradiction

namespace FunctionParameterInternals

/-- Every successful auxiliary parameter recovery commits a diagnostic. -/
theorem recoverParameterAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : FunctionParameter},
      recoverParameterAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverParameterAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverParameterAux at recovered
      split at recovered
      · unfold finishRecoveredParameter at recovered
        cases recovered
        simp [State.emit]
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            unfold finishRecoveredParameter at recovered
            cases recovered
            simp [State.emit]
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful complete parameter recovery commits a diagnostic. -/
theorem recoverParameter_diagnostics_ne_nil_onSuccess
    {input next : State} {value : FunctionParameter}
    (recovered : recoverParameter input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverParameter at recovered
  cases advanced : input.advance? with
  | none =>
      simp [advanced, rejectAt] at recovered
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      simp only [advanced] at recovered
      exact recoverParameterAux_diagnostics_ne_nil_onSuccess token.span
        token.span (afterToken.remainingCount + 1) recovered

/-- A missing-type error parameter always commits its constraint diagnostic. -/
theorem errorParameter_diagnostics_ne_nil_onSuccess
    (span : SourceSpan) (constraint : ParseConstraint)
    {input next : State} {value : FunctionParameter}
    (result : errorParameter span constraint input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold errorParameter emitDiagnostic modifyState at result
  simp only [bind, pure] at result
  cases result
  simp [State.emit]

private theorem namedParameterTail_error_success_hasDiagnostic
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input next : State} {span : SourceSpan}
    (result : namedParameterTail start marker name errorSpan input =
      .ok { span, value := .error } next) :
    next.diagnosticsRev ≠ [] := by
  unfold namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    unfold finishTypedParameter at finished
    cases typeValue : type.value <;>
      simp only [typeValue, emitDiagnostic, modifyState, bind, pure] at finished <;>
      cases finished
  · simp only [typed, Bool.false_eq_true, if_false] at result
    exact errorParameter_diagnostics_ne_nil_onSuccess errorSpan
      .namedParameterRequiresType result

private theorem ordinaryNamedParameter_error_success_hasDiagnostic
    {input next : State} {span : SourceSpan}
    (result : ordinaryNamedParameter input =
      .ok { span, value := .error } next) :
    next.diagnosticsRev ≠ [] := by
  unfold ordinaryNamedParameter at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true, emitDiagnostic, modifyState, bind] at rest
    exact namedParameterTail_error_success_hasDiagnostic name.span none name
      name.span rest
  · have absent : (name.value == ContextualKeyword.comptime.spelling) = false :=
      Bool.eq_false_iff.mpr warned
    simp only [absent, Bool.false_eq_true, if_false] at rest
    exact namedParameterTail_error_success_hasDiagnostic name.span none name
      name.span rest

private theorem comptimeNamedParameter_error_success_hasDiagnostic
    {input next : State} {span : SourceSpan}
    (result : comptimeNamedParameter input =
      .ok { span, value := .error } next) :
    next.diagnosticsRev ≠ [] := by
  unfold comptimeNamedParameter at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, tailResult⟩
  exact namedParameterTail_error_success_hasDiagnostic marker.span
    (some marker.span) name (SourceSpan.cover marker.span name.span) tailResult

private theorem namedParameterCore_error_success_hasDiagnostic
    {input next : State} {span : SourceSpan}
    (result : namedParameterCore input =
      .ok { span, value := .error } next) :
    next.diagnosticsRev ≠ [] := by
  unfold namedParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeNamedParameter_error_success_hasDiagnostic result
    · exact ordinaryNamedParameter_error_success_hasDiagnostic result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryNamedParameter_error_success_hasDiagnostic result

end FunctionParameterInternals

/-- Every successful named-parameter error retains at least one diagnostic. -/
theorem namedParameter_error_success_hasDiagnostic
    {input next : State} {span : SourceSpan}
    (result : namedParameter input = .ok { span, value := .error } next) :
    next.diagnosticsRev ≠ [] := by
  unfold namedParameter at result
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok value afterCore =>
      simp only [coreResult] at result
      cases result
      exact
        FunctionParameterInternals.namedParameterCore_error_success_hasDiagnostic
          coreResult
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) =
        .ok { span, value := .error } next at result
      split at result
      · contradiction
      · exact
          FunctionParameterInternals.recoverParameter_diagnostics_ne_nil_onSuccess
            result
  | invariant error =>
      simp [coreResult] at result

end Solcore.Syntax.Parser
