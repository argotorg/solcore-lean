import Solcore.Syntax.Internal.ParameterOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Parser.Internal.ParameterRecoveryTotality
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.Parser.Signatures
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Validity

/-!
Soundness of the parsers of parameters and predicates: each success and each rejection has
its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinarySoundnessProperties
/-! Exact executable ordinary successes of parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .parameter present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .parameter parsed).1⟩

namespace FunctionParameterInternals

/-- A true executable scan guard gives its exact declarative stop. -/
theorem functionParameterRecoveryStops_of_boundary
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = true) :
    DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · rcases tokenAt_of_isSymbol_eq_true .comma comma with
        ⟨span, token⟩
      exact .comma token
    · have commaFalse := Bool.eq_false_iff.mpr comma
      have rightParen : isSymbol input .rightParen = true := by
        simpa [atEndFalse, commaFalse] using boundary
      rcases tokenAt_of_isSymbol_eq_true .rightParen rightParen with
        ⟨span, token⟩
      exact .rightParen token

/-- Failed advancement is exact window-end or missing-carrier evidence. -/
theorem functionParameterRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.FunctionParameterRecoveryStops.missingToken
      inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- A present non-boundary token forces scan continuation. -/
theorem no_functionParameterRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.FunctionParameterRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | comma present =>
      have guard : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [guard] at boundary
  | rightParen present =>
      have guard : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [guard] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

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

/-- Every successful executable auxiliary scan follows the exact relation. -/
theorem recoverParameterAux_success_ordinary_sound (first : SourceSpan) :
    ∀ fuel last input parameter output,
      recoverParameterAux first last fuel input = .ok parameter output →
      DeclarativeGrammar.FunctionParameterRecoveryScanParses first last
        input.declarativeRemainder parameter output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input parameter output result
      simp [recoverParameterAux] at result
  | succ fuel inductionHypothesis =>
      intro last input parameter output result
      unfold recoverParameterAux at result
      by_cases boundary : (input.atEnd || isSymbol input .comma ||
          isSymbol input .rightParen) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredParameter at result
        cases result
        simpa [State.emit, State.declarativeRemainder] using
          (DeclarativeGrammar.FunctionParameterRecoveryScanParses.stop
            (first := first) (last := last)
            (functionParameterRecoveryStops_of_boundary input boundary))
      · have boundaryFalse : (input.atEnd || isSymbol input .comma ||
            isSymbol input .rightParen) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredParameter at result
            cases result
            simpa [State.emit, State.declarativeRemainder] using
              (DeclarativeGrammar.FunctionParameterRecoveryScanParses.stop
                (first := first) (last := last)
                (functionParameterRecoveryStops_of_advance?_eq_none input
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases advance?_state_shape advanced with ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next parameter output
              result
            rw [nextEq] at tail
            exact .next
              (no_functionParameterRecoveryStops_of_nonBoundary_token
                boundaryFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every complete executable function recovery includes its first token. -/
theorem recoverParameter_success_ordinary_sound
    {input output : State} {parameter : FunctionParameter}
    (result : recoverParameter input = .ok parameter output) :
    DeclarativeGrammar.FunctionParameterRecoveryParses
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases advance?_state_shape advanced with ⟨found, nextEq⟩
      have scan := recoverParameterAux_success_ordinary_sound token.span
        (next.remainingCount + 1) token.span next parameter output result
      rw [nextEq] at scan
      exact .recovered (tokenAt_of_peek?_eq_some found) scan

end FunctionParameterInternals

namespace LambdaParameterInternals

/-- Executable lambda recovery is the exact span-preserving retag. -/
theorem recoverLambdaParameter_success_ordinary_sound
    {input output : State} {parameter : LambdaParameter}
    (result : recoverLambdaParameter input = .ok parameter output) :
    DeclarativeGrammar.LambdaParameterRecoveryParses
      input.declarativeRemainder parameter output.declarativeRemainder := by
  unfold recoverLambdaParameter at result
  cases recoveredResult : FunctionParameterInternals.recoverParameter input with
  | invariant error => simp [recoveredResult] at result
  | reject failure rejected => simp [recoveredResult] at result
  | ok recovered afterRecovery =>
      simp only [recoveredResult] at result
      cases result
      exact .recovered
        (FunctionParameterInternals.recoverParameter_success_ordinary_sound
          recoveredResult)

end LambdaParameterInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinaryOutcomeSoundnessProperties
/-! Complete ordinary outcomes of standalone parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

private theorem recoveryRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.FunctionParameterRecoveryRejects
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.FunctionParameterRecoveryRejects.missingToken
      inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- Every complete executable recovery rejection is the unavailable first
token and preserves the full declarative remainder. -/
theorem recoverParameter_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact recoveryRejects_of_advance?_eq_none input advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverParameterAux_production_exists_ok token.span token.span next
        with ⟨parameter, output, success⟩
      rw [success] at result
      contradiction

/-- Package function-recovery success and rejection reflection. -/
theorem recoverParameter_ordinaryOutcome_sound :
    (∀ {input output : State} {parameter : FunctionParameter},
      recoverParameter input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterRecoveryParses
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverParameter input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverParameter_success_ordinary_sound,
    recoverParameter_reject_ordinary_sound⟩

end FunctionParameterInternals

namespace LambdaParameterInternals

/-- Lambda recovery propagates the exact unavailable-first-token rejection. -/
theorem recoverLambdaParameter_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverLambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverLambdaParameter at result
  cases recoveredResult : FunctionParameterInternals.recoverParameter input with
  | invariant error => simp [recoveredResult] at result
  | ok recovered output => simp [recoveredResult] at result
  | reject recoveryFailure recoveryRejected =>
      simp only [recoveredResult] at result
      cases result
      exact FunctionParameterInternals.recoverParameter_reject_ordinary_sound
        recoveredResult

/-- Package lambda-recovery success and rejection reflection. -/
theorem recoverLambdaParameter_ordinaryOutcome_sound :
    (∀ {input output : State} {parameter : LambdaParameter},
      recoverLambdaParameter input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterRecoveryParses
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverLambdaParameter input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverLambdaParameter_success_ordinary_sound,
    recoverLambdaParameter_reject_ordinary_sound⟩

/-- Re-export deterministic standalone lambda-recovery outcomes. -/
theorem recoverLambdaParameter_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.LambdaParameterRecoveryParses
      DeclarativeGrammar.LambdaParameterRecoveryRejects :=
  DeclarativeGrammar.lambdaParameterRecoveryDeterministicOutcomeSpec

end LambdaParameterInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterRecoveryDiagnosticProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterSoundnessProperties
/-! Diagnostic-free success soundness for named function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components_variant {alpha beta : Type} {first : Parser alpha}
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
    rcases bind_ok_components_variant result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components_variant rest with
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
  rcases bind_ok_components_variant result with
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
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components_variant rest with
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterDiagnosticReflectionProperties
/-! Diagnostic-free reflection for named function-parameter parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

private theorem finishTypedParameter_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (comptimeMarker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishTypedParameter start comptimeMarker name type) := by
  unfold finishTypedParameter
  dsimp only
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem errorParameter_reflectsDiagnosticFreeOnSuccess
    (span : SourceSpan) (constraint : ParseConstraint) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (errorParameter span constraint) := by
  unfold errorParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
  intro emitted
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem namedParameterTail_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (comptimeMarker : Option SourceSpan)
    (name : Identifier) (errorSpan : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (namedParameterTail start comptimeMarker name errorSpan) := by
  unfold namedParameterTail
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .colon .parameter)
    intro colon
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      typeExpr_reflectsDiagnosticFreeOnSuccess
    intro type
    exact finishTypedParameter_reflectsDiagnosticFreeOnSuccess start
      comptimeMarker name type
  · exact errorParameter_reflectsDiagnosticFreeOnSuccess errorSpan
      .namedParameterRequiresType

private theorem ordinaryNamedParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .parameter)
  intro name
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact namedParameterTail_reflectsDiagnosticFreeOnSuccess name.span none
      name name.span
  · exact namedParameterTail_reflectsDiagnosticFreeOnSuccess name.span none
      name name.span

private theorem comptimeNamedParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .comptime .parameter)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .parameter)
  intro name
  exact namedParameterTail_reflectsDiagnosticFreeOnSuccess marker.span
    (some marker.span) name (SourceSpan.cover marker.span name.span)

private theorem namedParameterCore_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess namedParameterCore := by
  intro input value next parsed diagnosticFree
  unfold namedParameterCore at parsed
  split at parsed
  · simp only [Bool.and_true] at parsed
    split at parsed
    · exact comptimeNamedParameter_reflectsDiagnosticFreeOnSuccess input
        value next parsed diagnosticFree
    · exact ordinaryNamedParameter_reflectsDiagnosticFreeOnSuccess input
        value next parsed diagnosticFree
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at parsed
    exact ordinaryNamedParameter_reflectsDiagnosticFreeOnSuccess input value
      next parsed diagnosticFree

private theorem recoverParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess recoverParameter := by
  intro input value next recovered diagnosticFree
  exact False.elim
    (recoverParameter_diagnostics_ne_nil_onSuccess recovered diagnosticFree)

end FunctionParameterInternals

/-- A diagnostic-free successful named-parameter parse had a diagnostic-free
input. -/
theorem namedParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess namedParameter := by
  intro input value next parsed diagnosticFree
  unfold namedParameter at parsed
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter afterCore =>
      simp only [coreResult] at parsed
      cases parsed
      exact
        FunctionParameterInternals.namedParameterCore_reflectsDiagnosticFreeOnSuccess
          input value next coreResult diagnosticFree
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)) = .ok value next at parsed
      split at parsed
      · contradiction
      · have emittedFree :=
          FunctionParameterInternals.recoverParameter_reflectsDiagnosticFreeOnSuccess
            (rewound.emit failure.toDiagnostic) value next parsed diagnosticFree
        simp [State.emit] at emittedFree
  | invariant error =>
      simp [coreResult] at parsed

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterCoreOrdinarySuccessSoundnessProperties
/-! Executable ordinary-success reflection for `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

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
    rcases bind_ok_components_variant result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components_variant rest with
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
  rcases bind_ok_components_variant result with
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
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components_variant rest with
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterCoreOrdinaryRejectionSoundnessProperties
/-! Executable ordinary-rejection reflection for `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_eq_ok_of_present
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (present : isContextual input value = true) :
    ∃ token, contextual value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isContextual State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      refine ⟨token, ?_⟩
      unfold contextual acceptToken
      simp only [found, present, ↓reduceIte]

private theorem identifier_exists_ok_of_offset_identifier
    {input : State}
    (present : (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true) :
    ∃ name output, identifier .parameter
      { input with cursor := input.cursor + 1 } = .ok name output := by
  unfold State.peekOffsetKind? at present
  cases found : input.peekOffset? 1 with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present
      all_goals try contradiction
      case identifier text =>
        let afterMarker : State := { input with cursor := input.cursor + 1 }
        have current : afterMarker.peek? = some {
            span
            value := TokenKind.identifier text
          } := by
          simpa only [afterMarker, State.peek?, State.peekOffset?, Nat.add_comm]
            using found
        have rawResult : rawIdentifier .parameter afterMarker = .ok
            { span, value := text }
            { afterMarker with cursor := afterMarker.cursor + 1 } := by
          unfold rawIdentifier
          rw [current]
        by_cases warned : text.toList.contains '-'
        · exact ⟨{ span, value := text },
            ({ afterMarker with cursor := afterMarker.cursor + 1 }).emit {
              span
              kind := .invalidIdentifierHyphen text
            }, by
              unfold identifier
              rw [rawResult]
              simp only [warned, if_true]⟩
        · have warnedFalse : text.toList.contains '-' = false :=
            Bool.eq_false_iff.mpr warned
          exact ⟨{ span, value := text },
            { afterMarker with cursor := afterMarker.cursor + 1 }, by
              unfold identifier
              rw [rawResult]
              simp only [warnedFalse, Bool.false_eq_true, if_false]⟩

namespace FunctionParameterInternals

private theorem namedParameterTail_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input rejected : State} {failure : Failure}
    (result : namedParameterTail start marker name errorSpan input =
      .reject failure rejected) :
    ∃ colonSpan afterColon,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      typeRejects afterColon rejected.declarativeRemainder := by
  unfold namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter typed with
      ⟨colon, colonResult⟩
    simp only [typed, if_true, colonResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact ⟨colon.span, _,
          symbol_success_exactTokenParses .colon .parameter colonResult,
          typeRejectSound typeResult⟩
    | ok type afterType =>
        simp only [typeResult] at result
        unfold finishTypedParameter at result
        cases typeValue : type.value <;>
          simp [typeValue, emitDiagnostic, modifyState, bind, pure] at result
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    unfold errorParameter at result
    simp [emitDiagnostic, modifyState, bind, pure] at result

private theorem ordinaryNamedParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (prefixAbsent : DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
      input.declarativeRemainder)
    (result : ordinaryNamedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ordinaryNamedParameter at result
  simp only [bind] at result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [nameResult] at result
      cases result
      exact .ordinaryName prefixAbsent
        (identifier_reject_sound .parameter nameResult)
  | ok name afterName =>
      simp only [nameResult] at result
      have nameParsed := identifier_success_sound .parameter nameResult
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
          at result
        rcases namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name.span none name name.span result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan prefixAbsent nameParsed
          (by simpa [State.emit, State.declarativeRemainder] using colonParsed)
          typeRejected
      · have warnedFalse :
          (name.value == ContextualKeyword.comptime.spelling) = false :=
          Bool.eq_false_iff.mpr warned
        simp only [warnedFalse, Bool.false_eq_true, if_false] at result
        rcases namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name.span none name name.span result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan prefixAbsent nameParsed colonParsed
          typeRejected

private theorem comptimeNamedParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .comptime = true)
    (namePresent : (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true)
    (result : comptimeNamedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_present .comptime .parameter markerPresent with
    ⟨marker, markerResult⟩
  rcases identifier_exists_ok_of_offset_identifier namePresent with
    ⟨name, afterName, nameResult⟩
  unfold comptimeNamedParameter at result
  simp only [bind, markerResult, nameResult] at result
  rcases namedParameterTail_reject_ordinary_sound typeRejects typeRejectSound
      marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) result with
    ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
  exact .comptimeType marker.span colonSpan
    (contextual_success_exactTokenParses .comptime .parameter markerResult)
    (identifier_success_sound .parameter nameResult) colonParsed typeRejected

/-- Every executable Core rejection follows the exact selected relation. -/
theorem namedParameterCore_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : namedParameterCore input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold namedParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeNamedParameter_reject_ordinary_sound typeRejects
        typeRejectSound (by simp_all) (by simp_all) result
    · exact ordinaryNamedParameter_reject_ordinary_sound typeRejects
        typeRejectSound (comptimePrefixAbsent_of_core_false (by simp_all))
          result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryNamedParameter_reject_ordinary_sound typeRejects
      typeRejectSound (comptimePrefixAbsent_of_core_false (by simp_all))
        result

end FunctionParameterInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterCoreOrdinaryOutcomeSoundnessProperties
/-! Complete executable ordinary outcome of `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

/-- Package exact ordinary success and rejection of the Core parser. -/
theorem namedParameterCore_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {parameter : FunctionParameter},
      namedParameterCore input = .ok parameter output →
        DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      namedParameterCore input = .reject failure rejected →
        DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨namedParameterCore_success_ordinary_sound typeOrdinary typeSuccessSound,
    namedParameterCore_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Re-export the deterministic Core relation contract. -/
theorem namedParameterCore_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FunctionParameterCoreOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.FunctionParameterCoreRejects typeRejects) :=
  DeclarativeGrammar.functionParameterCoreDeterministicOutcomeSpec
    typeOutcomes

end Solcore.Syntax.Parser.FunctionParameterInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterCoreOrdinarySuccessSoundnessProperties
/-! Executable ordinary-success reflection for `lambdaParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem comptimePrefixAbsent_of_core_false_variant {input : State}
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
    rcases bind_ok_components_variant result with
      ⟨colon, afterColon, colonResult, rest⟩
    rcases bind_ok_components_variant rest with
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
    rcases bind_ok_components_variant result with
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
  rcases bind_ok_components_variant result with
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
  rcases bind_ok_components_variant result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨name, afterName, nameResult, tailResult⟩
  unfold comptimeLambdaParameterTail getState at tailResult
  simp only [bind] at tailResult
  by_cases typed : isSymbol afterName .colon
  · simp only [typed, if_true] at tailResult
    rcases bind_ok_components_variant tailResult with
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
        (comptimePrefixAbsent_of_core_false_variant (by simp_all))
        (ordinaryLambdaParameter_success_ordinary_sound typeOrdinary
          typeSuccessSound result)
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact .ordinary (comptimePrefixAbsent_of_core_false_variant (by simp_all))
      (ordinaryLambdaParameter_success_ordinary_sound typeOrdinary
        typeSuccessSound result)

end LambdaParameterInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterCoreOrdinaryRejectionSoundnessProperties
/-! Executable ordinary-rejection reflection for `lambdaParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace LambdaParameterInternals

private theorem namedParameterTail_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input rejected : State} {failure : Failure}
    (result : FunctionParameterInternals.namedParameterTail start marker name
      errorSpan input = .reject failure rejected) :
    ∃ colonSpan afterColon,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      typeRejects afterColon rejected.declarativeRemainder := by
  unfold FunctionParameterInternals.namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter typed with
      ⟨colon, colonResult⟩
    simp only [typed, if_true, colonResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact ⟨colon.span, _,
          symbol_success_exactTokenParses .colon .parameter colonResult,
          typeRejectSound typeResult⟩
    | ok type afterType =>
        simp only [typeResult] at result
        unfold FunctionParameterInternals.finishTypedParameter at result
        cases typeValue : type.value <;>
          simp [typeValue, emitDiagnostic, modifyState, bind, pure] at result
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    unfold FunctionParameterInternals.errorParameter at result
    simp [emitDiagnostic, modifyState, bind, pure] at result

private theorem ordinaryLambdaParameterTail_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (name : Identifier) {input rejected : State} {failure : Failure}
    (result : ordinaryLambdaParameterTail name input =
      .reject failure rejected) :
    ∃ colonSpan afterColon,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      typeRejects afterColon rejected.declarativeRemainder := by
  unfold ordinaryLambdaParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    cases tailResult : FunctionParameterInternals.namedParameterTail
        name.span none name name.span input with
    | invariant error => simp [tailResult] at result
    | ok parameter output => simp [tailResult, pure] at result
    | reject tailFailure tailRejected =>
        simp only [tailResult] at result
        cases result
        exact namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name.span none name name.span tailResult
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp [typedFalse, pure] at result

private theorem ordinaryLambdaParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (comptimeAbsent :
      ¬ DeclarativeGrammar.ComptimeLambdaParameterStartsAt
        input.declarativeRemainder)
    (result : ordinaryLambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ordinaryLambdaParameter at result
  simp only [bind] at result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [nameResult] at result
      cases result
      exact .ordinaryName comptimeAbsent
        (identifier_reject_sound .parameter nameResult)
  | ok name afterName =>
      simp only [nameResult] at result
      have nameParsed := identifier_success_sound .parameter nameResult
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
          at result
        rcases ordinaryLambdaParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan comptimeAbsent nameParsed
          (by simpa [State.emit, State.declarativeRemainder] using colonParsed)
          typeRejected
      · have warnedFalse :
          (name.value == ContextualKeyword.comptime.spelling) = false :=
          Bool.eq_false_iff.mpr warned
        simp only [warnedFalse, Bool.false_eq_true, if_false] at result
        rcases ordinaryLambdaParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan comptimeAbsent nameParsed colonParsed
          typeRejected

private theorem comptimeLambdaParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .comptime = true)
    (namePresent : (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true)
    (result : comptimeLambdaParameter input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_present .comptime .parameter markerPresent with
    ⟨marker, markerResult⟩
  rcases identifier_exists_ok_of_offset_identifier namePresent with
    ⟨name, afterName, nameResult⟩
  unfold comptimeLambdaParameter at result
  simp only [bind, markerResult, nameResult] at result
  unfold comptimeLambdaParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol afterName .colon
  · simp only [typed, if_true] at result
    cases tailResult : FunctionParameterInternals.namedParameterTail
        marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) afterName with
    | invariant error => simp [tailResult] at result
    | ok parameter output => simp [tailResult, pure] at result
    | reject tailFailure tailRejected =>
        simp only [tailResult] at result
        cases result
        rcases namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) tailResult with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .comptimeType marker.span colonSpan
          (contextual_success_exactTokenParses .comptime .parameter
            markerResult)
          (identifier_success_sound .parameter nameResult) colonParsed
          typeRejected
  · have typedFalse : isSymbol afterName .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    unfold FunctionParameterInternals.errorParameter at result
    simp [emitDiagnostic, modifyState, bind, pure] at result

/-- Every executable Core rejection follows the exact selected relation. -/
theorem lambdaParameterCore_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : lambdaParameterCore input = .reject failure rejected) :
    DeclarativeGrammar.LambdaParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold lambdaParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeLambdaParameter_reject_ordinary_sound typeRejects
        typeRejectSound (by simp_all) (by simp_all) result
    · exact ordinaryLambdaParameter_reject_ordinary_sound typeRejects
        typeRejectSound (comptimePrefixAbsent_of_core_false_variant (by simp_all))
          result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryLambdaParameter_reject_ordinary_sound typeRejects
      typeRejectSound (comptimePrefixAbsent_of_core_false_variant (by simp_all)) result

end LambdaParameterInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterCoreOrdinaryOutcomeSoundnessProperties
/-! Complete executable ordinary outcome of `lambdaParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

/-- Package exact ordinary success and rejection of the Core parser. -/
theorem lambdaParameterCore_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {parameter : LambdaParameter},
      lambdaParameterCore input = .ok parameter output →
        DeclarativeGrammar.LambdaParameterCoreOrdinaryParses typeOrdinary
          input.declarativeRemainder parameter output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      lambdaParameterCore input = .reject failure rejected →
        DeclarativeGrammar.LambdaParameterCoreRejects typeRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaParameterCore_success_ordinary_sound typeOrdinary
      typeSuccessSound,
    lambdaParameterCore_reject_ordinary_sound typeRejects typeRejectSound⟩

/-- Re-export the deterministic Core relation contract. -/
theorem lambdaParameterCore_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaParameterCoreOrdinaryParses typeOrdinary)
      (DeclarativeGrammar.LambdaParameterCoreRejects typeRejects) :=
  DeclarativeGrammar.lambdaParameterCoreDeterministicOutcomeSpec typeOutcomes

end Solcore.Syntax.Parser.LambdaParameterInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSoundnessProperties
/-! Success soundness for one trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful predicate follows its exact recursive type grammar. -/
theorem predicate_success_sound {input next : State} {value : Predicate}
    (result : predicate input = .ok value next) :
    DeclarativeGrammar.PredicateParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold predicate at result
  rcases predicateBind_ok_components result with
    ⟨subject, afterSubject, subjectResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨colon, afterColon, colonResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨traitName, afterName, nameResult, rest⟩
  rcases predicateBind_ok_components rest with
    ⟨arguments, afterArguments, argumentsResult, finished⟩
  cases finished
  have argumentsGrammar := parseNamedTypeArguments_success_sound typeExpr
    typeExpr_success_sound typeExpr_preservesTokenWindow argumentsResult
  cases arguments <;>
    exact .parsed colon.span
      (typeExpr_success_sound subjectResult)
      (symbol_success_exactTokenParses .colon .typeExpr colonResult)
      (identifier_success_sound .typeExpr nameResult) argumentsGrammar

/-- Predicate grammar soundness composes with source validity. -/
theorem predicate_success_sound_and_validFor {input next : State}
    {value : Predicate} (inputValid : input.ValidFor)
    (result : predicate input = .ok value next) :
    DeclarativeGrammar.PredicateParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      Predicate.ValidFor input.file value := by
  refine ⟨predicate_success_sound result, ?_⟩
  have valid := predicate_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.BarePredicateSequenceSoundnessProperties
/-! Success soundness for unparenthesized predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

private theorem typeExprStartsAt_of_isKeyword_function
    {input : State} (present : isKeyword input .functionKw = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .keyword .functionKw) = true at present
      have parsed : keyword .functionKw .typeExpr input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold keyword acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, .keyword .functionKw,
        (keyword_ok_tokenAt .functionKw .typeExpr parsed).1, .function⟩

private theorem typeExprStartsAt_of_isSymbol
    (symbol : Symbol) (starts : DeclarativeGrammar.TypeExprStartToken
      (.symbol symbol)) {input : State}
    (present : isSymbol input symbol = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol symbol) = true at present
      have parsed : Solcore.Syntax.Parser.symbol symbol .typeExpr input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold Solcore.Syntax.Parser.symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, .symbol symbol,
        (symbol_ok_tokenAt symbol .typeExpr parsed).1, starts⟩

private theorem typeExprStartsAt_of_isIdentifier {input : State}
    (present : isIdentifier input = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  unfold isIdentifier State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      cases kindEq : token.value <;> simp [kindEq] at present
      case identifier text =>
        have tokenEq : token = {
            span := token.span
            value := .identifier text
          } := by
          rcases token with ⟨span, kind⟩
          simp only at kindEq ⊢
          subst kind
          rfl
        have tokenAt := tokenAt_of_peek?_eq_some found
        rw [tokenEq] at tokenAt
        exact ⟨token.span, .identifier text, tokenAt, .identifier text⟩

/-- Positive executable type lookahead is exact declarative start evidence. -/
theorem typeExprStartsAt_of_startsTypeExpr_eq_true {input : State}
    (present : startsTypeExpr input = true) :
    DeclarativeGrammar.TypeExprStartsAt input.declarativeRemainder := by
  simp only [startsTypeExpr, Bool.or_eq_true] at present
  rcases present with left | identifierPresent
  · rcases left with left | tuplePresent
    · rcases left with functionPresent | proxyPresent
      · exact typeExprStartsAt_of_isKeyword_function functionPresent
      · exact typeExprStartsAt_of_isSymbol .at .proxy proxyPresent
    · exact typeExprStartsAt_of_isSymbol .leftParen .tuple tuplePresent
  · exact typeExprStartsAt_of_isIdentifier identifierPresent

private theorem startsTypeExpr_eq_true_of_typeExprStartsAt {input : State}
    (present : DeclarativeGrammar.TypeExprStartsAt
      input.declarativeRemainder) : startsTypeExpr input = true := by
  rcases present with ⟨span, kind, tokenAt, starts⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at tokenAt
  have found : input.peek? = some { span, value := kind } := by
    unfold State.peek?
    simp only [tokenAt.1, ↓reduceIte, tokenAt.2]
  cases starts <;>
    (unfold startsTypeExpr isKeyword isSymbol isIdentifier State.peekKind?
     rw [found]
     rfl)

private theorem typeExprAbsentAt_of_startsTypeExpr_eq_false {input : State}
    (absent : startsTypeExpr input = false) :
    DeclarativeGrammar.TypeExprAbsentAt input.declarativeRemainder := by
  intro present
  have contradictory := startsTypeExpr_eq_true_of_typeExprStartsAt present
  rw [absent] at contradictory
  contradiction

private theorem barePredicatesTail_success_sound_strong
    (first : Predicate) : ∀ fuel last tailRev input values next,
      barePredicatesTail first fuel last tailRev input = .ok values next →
      ∃ suffix finalSpan,
        values = {
          span := SourceSpan.cover first.span finalSpan
          elements := {
            head := first
            tail := tailRev.reverse ++ suffix
          }
        } ∧
        DeclarativeGrammar.BarePredicateTailParses last.span
          input.declarativeRemainder suffix finalSpan
          next.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input values next result
      simp [barePredicatesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input values next result
      unfold barePredicatesTail at result
      split at result
      · rename_i commaPresent
        cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            have commaGrammar := symbol_success_exactTokenParses .comma
              .typeExpr commaResult
            split at result
            · rename_i typePresent
              cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at result
              | reject failure rejected => simp [predicateResult] at result
              | ok value afterPredicate =>
                  simp only [predicateResult] at result
                  rcases inductionHypothesis value (value :: tailRev)
                      afterPredicate values next result with
                    ⟨suffix, finalSpan, valuesEq, tailGrammar⟩
                  refine ⟨value :: suffix, finalSpan, ?_,
                    .next commaGrammar
                      (typeExprStartsAt_of_startsTypeExpr_eq_true typePresent)
                      (predicate_success_sound predicateResult) tailGrammar⟩
                  rw [valuesEq]
                  simp [List.reverse_cons, List.append_assoc]
            · rename_i typeAbsent
              cases result
              refine ⟨[], comma.span, by simp, .trailing commaGrammar ?_⟩
              exact typeExprAbsentAt_of_startsTypeExpr_eq_false
                (Bool.eq_false_iff.mpr typeAbsent)
      · rename_i commaAbsent
        cases result
        refine ⟨[], last.span, by simp,
          .done (symbolAbsentAt_of_isSymbol_eq_false .comma ?_)⟩
        exact Bool.eq_false_iff.mpr commaAbsent

/-- Every successful bare sequence follows its exact retained grammar. -/
theorem barePredicates_success_sound {input next : State}
    {values : PredicateSequence}
    (result : barePredicates input = .ok values next) :
    DeclarativeGrammar.BarePredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold barePredicates at result
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases barePredicatesTail_success_sound_strong first
          (afterFirst.remainingCount + 1) first [] afterFirst values next
          result with ⟨rest, finalSpan, valuesEq, tailGrammar⟩
      rw [valuesEq]
      simpa using DeclarativeGrammar.BarePredicateSequenceParses.parsed
        (predicate_success_sound firstResult) tailGrammar

/-- Bare sequence grammar soundness composes with source validity. -/
theorem barePredicates_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : barePredicates input = .ok values next) :
    DeclarativeGrammar.BarePredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨barePredicates_success_sound result, ?_⟩
  have valid := barePredicates_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.GroupedPredicateSequenceSoundnessProperties
/-! Success soundness for parenthesized predicate sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PredicateInternals

/-- Every successful grouped sequence follows the generic delimiter grammar. -/
theorem groupedPredicates_success_sound {input next : State}
    {values : PredicateSequence}
    (result : groupedPredicates input = .ok values next) :
    DeclarativeGrammar.GroupedPredicateSequenceParses
      input.declarativeRemainder values next.declarativeRemainder := by
  unfold groupedPredicates at result
  rcases predicateBind_ok_components result with
    ⟨parsed, afterParsed, parsedResult, finished⟩
  have grammar := delimited_nonempty_trailing_success_sound .leftParen
    .rightParen predicate DeclarativeGrammar.PredicateParses .typeExpr
    .topLevel predicate_success_sound predicate_preservesTokenWindow
    parsedResult
  cases elements : parsed.elements with
  | nil =>
      simp [elements] at finished
  | cons head tail =>
      simp only [elements, pure] at finished
      have parsedEq : parsed = {
          span := parsed.span
          elements := head :: tail
        } := by
        rcases parsed with ⟨span, parsedElements⟩
        simp only at elements ⊢
        rw [elements]
      rw [parsedEq] at grammar
      cases finished
      simpa [DeclarativeGrammar.GroupedPredicateSequenceParses,
        NonemptyList.toList] using grammar

/-- Grouped sequence grammar soundness composes with source validity. -/
theorem groupedPredicates_success_sound_and_validFor {input next : State}
    {values : PredicateSequence} (inputValid : input.ValidFor)
    (result : groupedPredicates input = .ok values next) :
    DeclarativeGrammar.GroupedPredicateSequenceParses
        input.declarativeRemainder values next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file values := by
  refine ⟨groupedPredicates_success_sound result, ?_⟩
  have valid := groupedPredicates_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser.PredicateInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.PredicateSequenceDiagnosticReflectionProperties
/-! Diagnostic-free reflection for predicates, their sequences, and `where`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem requireNonemptyForPredicate_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList TypeExpr) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireNonempty values phase) := by
  intro input nonempty next parsed diagnosticFree
  unfold requireNonempty at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements, pure] at parsed
      cases parsed
      exact diagnosticFree

private theorem parseNamedTypeArguments_reflectsDiagnosticFreeForPredicate
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (parseNamedTypeArguments nested) := by
  unfold parseNamedTypeArguments
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false nested
        .typeExpr .typeExpr nestedReflects)
    intro values
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireNonemptyForPredicate_reflectsDiagnosticFreeOnSuccess values
        .typeExpr)
    intro nonempty
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- One predicate cannot erase diagnostics from its recursive type stages. -/
theorem predicate_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess predicate := by
  unfold predicate
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    typeExpr_reflectsDiagnosticFreeOnSuccess
  intro subject
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .colon .typeExpr)
  intro colon
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .typeExpr)
  intro traitName
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseNamedTypeArguments_reflectsDiagnosticFreeForPredicate typeExpr
      typeExpr_reflectsDiagnosticFreeOnSuccess)
  intro arguments
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

namespace PredicateInternals

/-- Parenthesized predicate parsing reflects through its generic list. -/
theorem groupedPredicates_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess groupedPredicates := by
  unfold groupedPredicates
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen false
      predicate .typeExpr .topLevel
      predicate_reflectsDiagnosticFreeOnSuccess)
  intro values
  cases values.elements with
  | nil =>
      intro input result next parsed diagnosticFree
      simp at parsed
  | cons head tail =>
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem barePredicatesTail_reflectsDiagnosticFreeOnSuccess
    (first : Predicate) : ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (barePredicatesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input values next parsed diagnosticFree
      simp [barePredicatesTail] at parsed
  | succ fuel inductionHypothesis =>
      intro last tailRev input values next parsed diagnosticFree
      unfold barePredicatesTail at parsed
      split at parsed
      · cases commaResult : symbol .comma .typeExpr input with
        | invariant error => simp [commaResult] at parsed
        | reject failure rejected => simp [commaResult] at parsed
        | ok comma afterComma =>
            simp only [commaResult] at parsed
            split at parsed
            · cases predicateResult : predicate afterComma with
              | invariant error => simp [predicateResult] at parsed
              | reject failure rejected => simp [predicateResult] at parsed
              | ok value afterPredicate =>
                  simp only [predicateResult] at parsed
                  have afterPredicateFree := inductionHypothesis value
                    (value :: tailRev) afterPredicate values next parsed
                    diagnosticFree
                  have afterCommaFree :=
                    predicate_reflectsDiagnosticFreeOnSuccess afterComma value
                      afterPredicate predicateResult afterPredicateFree
                  exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                    .typeExpr input comma afterComma commaResult afterCommaFree
            · have afterCommaFree : afterComma.diagnosticsRev = [] := by
                cases parsed
                exact diagnosticFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma .typeExpr
                input comma afterComma commaResult afterCommaFree
      · cases parsed
        exact diagnosticFree

/-- A bare predicate sequence reflects through its first item and fuel loop. -/
theorem barePredicates_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess barePredicates := by
  intro input values next parsed diagnosticFree
  unfold barePredicates at parsed
  cases firstResult : predicate input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first afterFirst =>
      simp only [firstResult] at parsed
      have afterFirstFree := barePredicatesTail_reflectsDiagnosticFreeOnSuccess
        first (afterFirst.remainingCount + 1) first [] afterFirst values next
        parsed diagnosticFree
      exact predicate_reflectsDiagnosticFreeOnSuccess input first afterFirst
        firstResult afterFirstFree

/-- Transactional grouped-or-bare dispatch cannot erase diagnostics. -/
theorem predicateSequence_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess predicateSequence := by
  intro input values next parsed diagnosticFree
  unfold predicateSequence at parsed
  split at parsed
  · exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
      groupedPredicates_reflectsDiagnosticFreeOnSuccess
      barePredicates_reflectsDiagnosticFreeOnSuccess input values next parsed
      diagnosticFree
  · exact barePredicates_reflectsDiagnosticFreeOnSuccess input values next
      parsed diagnosticFree

end PredicateInternals

/-- Optional `where` parsing reflects through its marker and chosen sequence. -/
theorem whereClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess whereClause := by
  unfold whereClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .where .typeExpr)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      PredicateInternals.predicateSequence_reflectsDiagnosticFreeOnSuccess
    intro predicates
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.Signature
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A generic parameter list starts at its opening angle bracket. -/
theorem genericParameters_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess genericParameters (·.span) := by
  unfold genericParameters
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimited_startsAtCurrentTokenOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel)
  intro values input result next parsed
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil =>
      simp only [elements] at parsed
      contradiction
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      rfl

/-- Complete function signatures retain only source-valid syntax. -/
theorem functionSignature_validFor (location : FunctionLocation) :
    (functionSignature location).ValidFor FunctionSignature.ValidFor :=
  functionSignature_validFor_of_span location whereClause_validFor
    (fun _ _ _ inputValid parsed =>
      functionSignature_span_validOnSuccess location inputValid parsed)

/-- Complete signatures preserve token windows when `where` parsing does. -/
theorem functionSignature_preservesTokenWindow_of_where (location : FunctionLocation)
    (whereWindow : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokenWindow (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .functionKw .topItem)
  intro functionToken
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .topItem)
  intro name
  apply Parser.bind_preservesTokenWindow
    optionalGenericParameters_preservesTokenWindow
  intro genericParameters
  apply Parser.bind_preservesTokenWindow functionParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow
    (functionModifiers_preservesTokenWindow location)
  intro modifiers
  apply Parser.bind_preservesTokenWindow returnClause_preservesTokenWindow
  intro returnsClause
  apply Parser.bind_preservesTokenWindow whereWindow
  intro parsedWhereClause
  exact Parser.pure_preservesTokenWindow _

theorem functionSignature_preservesTokensOnSuccess_of_where
    (location : FunctionLocation)
    (whereWindow : Parser.PreservesTokenWindow whereClause) :
    Parser.PreservesTokensOnSuccess (functionSignature location) :=
  (functionSignature_preservesTokenWindow_of_where location whereWindow
    ).preservesTokensOnSuccess

/-- Complete signatures never rewind when `where` parsing is monotone. -/
theorem functionSignature_cursorMonotoneOnSuccess_of_where
    (location : FunctionLocation)
    (whereCursor : Parser.CursorMonotoneOnSuccess whereClause) :
    Parser.CursorMonotoneOnSuccess (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .functionKw .topItem)
  intro functionToken
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .topItem)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    optionalGenericParameters_cursorMonotoneOnSuccess
  intro genericParameters
  apply Parser.bind_cursorMonotoneOnSuccess
    functionParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (functionModifiers_cursorMonotoneOnSuccess location)
  intro modifiers
  apply Parser.bind_cursorMonotoneOnSuccess
    returnClause_cursorMonotoneOnSuccess
  intro returnsClause
  apply Parser.bind_cursorMonotoneOnSuccess whereCursor
  intro parsedWhereClause
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- Complete signatures preserve token windows. -/
theorem functionSignature_preservesTokenWindow (location : FunctionLocation) :
    Parser.PreservesTokenWindow (functionSignature location) :=
  functionSignature_preservesTokenWindow_of_where location
    whereClause_preservesTokenWindow

theorem functionSignature_preservesTokensOnSuccess
    (location : FunctionLocation) :
    Parser.PreservesTokensOnSuccess (functionSignature location) :=
  (functionSignature_preservesTokenWindow location).preservesTokensOnSuccess

/-- Complete signatures never rewind. -/
theorem functionSignature_cursorMonotoneOnSuccess
    (location : FunctionLocation) :
    Parser.CursorMonotoneOnSuccess (functionSignature location) :=
  functionSignature_cursorMonotoneOnSuccess_of_where location
    whereClause_cursorMonotoneOnSuccess

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.SignatureLeafDiagnosticReflectionProperties`
-/

/-! Diagnostic-free reflection for non-predicate function-signature leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem requireGenericParameters_reflectsDiagnosticFreeOnSuccess
    (values : DelimitedList Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireGenericParameters values) := by
  intro input parameters next parsed diagnosticFree
  unfold requireGenericParameters at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements, pure] at parsed
      cases parsed
      exact diagnosticFree

/-- Generic-parameter parsing cannot erase an incoming diagnostic. -/
theorem genericParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess genericParameters := by
  unfold genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .less .greater false
      (identifier .parameter) .parameter .topLevel
      (identifier_reflectsDiagnosticFreeOnSuccess .parameter))
  exact requireGenericParameters_reflectsDiagnosticFreeOnSuccess

/-- Optional generic-parameter parsing reflects diagnostic freedom. -/
theorem optionalGenericParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalGenericParameters := by
  unfold optionalGenericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      genericParameters_reflectsDiagnosticFreeOnSuccess
    intro values
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

/-- Function-parameter delimiters and elements cannot erase diagnostics. -/
theorem functionParameters_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess functionParameters := by
  unfold functionParameters
  exact delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
    namedParameter .parameter .topLevel
      namedParameter_reflectsDiagnosticFreeOnSuccess

/-- One optional hard-keyword modifier reflects diagnostic freedom. -/
theorem optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess
    (keywordValue : HardKeyword) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (optionalFunctionModifier keywordValue) := by
  unfold optionalFunctionModifier
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (keyword_reflectsDiagnosticFreeOnSuccess keywordValue .parameter)
    intro marker
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private def modifierPolicyForReflection (location : FunctionLocation)
    (keywordValue : HardKeyword) (marker : Option SourceSpan) : Parser Unit :=
  match location, marker with
  | .module, some span => emitDiagnostic {
      span
      kind := .constraintViolation (.modifierOutsideContract keywordValue)
    }
  | _, _ => pure ()

private def finishFunctionModifiersForReflection (location : FunctionLocation)
    (publicMarker payableMarker : Option SourceSpan) :
    Parser FunctionModifiers := do
  let _ ← modifierPolicyForReflection location .publicKw publicMarker
  let _ ← modifierPolicyForReflection location .payableKw payableMarker
  pure { publicMarker, payableMarker }

private theorem modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) (keywordValue : HardKeyword)
    (marker : Option SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (modifierPolicyForReflection location keywordValue marker) := by
  unfold modifierPolicyForReflection
  cases location <;> cases marker
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  · exact emitDiagnostic_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess ()

private theorem finishFunctionModifiersForReflection_reflectsDiagnosticFree
    (location : FunctionLocation) (publicMarker payableMarker : Option SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishFunctionModifiersForReflection location publicMarker
        payableMarker) := by
  unfold finishFunctionModifiersForReflection
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess location
      .publicKw publicMarker)
  intro publicChecked
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (modifierPolicyForReflection_reflectsDiagnosticFreeOnSuccess location
      .payableKw payableMarker)
  intro payableChecked
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Location-policy diagnostics are only added, never erased. -/
theorem functionModifiers_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) :
    Parser.ReflectsDiagnosticFreeOnSuccess (functionModifiers location) := by
  unfold functionModifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess .publicKw)
  intro publicMarker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (optionalFunctionModifier_reflectsDiagnosticFreeOnSuccess .payableKw)
  intro payableMarker
  change Parser.ReflectsDiagnosticFreeOnSuccess
    (finishFunctionModifiersForReflection location publicMarker payableMarker)
  exact finishFunctionModifiersForReflection_reflectsDiagnosticFree location
    publicMarker payableMarker

/-- Optional return-clause parsing cannot erase incoming diagnostics. -/
theorem returnClause_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess returnClause := by
  unfold returnClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .returns .typeExpr)
    intro marker
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
        typeExpr .typeExpr .typeExpr
        typeExpr_reflectsDiagnosticFreeOnSuccess)
    intro types
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionSignatureDiagnosticReflectionProperties
/-! Diagnostic-free reflection for complete named-function signatures. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Complete signature parsing cannot erase an incoming diagnostic. -/
theorem functionSignature_reflectsDiagnosticFreeOnSuccess
    (location : FunctionLocation) :
    Parser.ReflectsDiagnosticFreeOnSuccess (functionSignature location) := by
  unfold functionSignature
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .topItem)
  intro functionToken
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .topItem)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalGenericParameters_reflectsDiagnosticFreeOnSuccess
  intro genericParameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    functionParameters_reflectsDiagnosticFreeOnSuccess
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (functionModifiers_reflectsDiagnosticFreeOnSuccess location)
  intro modifiers
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    returnClause_reflectsDiagnosticFreeOnSuccess
  intro returnsClause
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    whereClause_reflectsDiagnosticFreeOnSuccess
  intro whereClause
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionModifierSoundnessProperties
/-! Success soundness for ordered function modifiers and location policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- One optional modifier preserves keyword priority and exact state. -/
theorem optionalFunctionModifier_success_sound (keywordValue : HardKeyword)
    {input next : State} {marker : Option SourceSpan}
    (result : optionalFunctionModifier keywordValue input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses keywordValue
      input.declarativeRemainder marker next.declarativeRemainder := by
  unfold optionalFunctionModifier getState at result
  simp only [bind] at result
  by_cases present : isKeyword input keywordValue
  · simp only [present, if_true] at result
    cases markerResult : keyword keywordValue .parameter input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok token afterMarker =>
        simp only [markerResult, pure] at result
        cases result
        exact .present token.span
          (keyword_success_exactTokenParses keywordValue .parameter
            markerResult)
  · have absent : isKeyword input keywordValue = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (keywordAbsentAt_of_isKeyword_eq_false keywordValue absent)

/-- Ordered modifier grammar soundness composes with source validity. -/
theorem optionalFunctionModifier_success_sound_and_validFor
    (keywordValue : HardKeyword) {input next : State}
    {marker : Option SourceSpan} (inputValid : input.ValidFor)
    (result : optionalFunctionModifier keywordValue input = .ok marker next) :
    DeclarativeGrammar.OptionalFunctionModifierParses keywordValue
        input.declarativeRemainder marker next.declarativeRemainder ∧
      Option.ValidFor (fun file span => span.ValidFor file) input.file
        marker := by
  refine ⟨optionalFunctionModifier_success_sound keywordValue result, ?_⟩
  have valid := optionalFunctionModifier_validFor keywordValue input inputValid
  rw [result] at valid
  exact valid.1

/-- Every success retains the fixed optional `public`-then-`payable` order. -/
theorem functionModifiers_success_sound (location : FunctionLocation)
    {input next : State} {modifiers : FunctionModifiers}
    (result : functionModifiers location input = .ok modifiers next) :
    DeclarativeGrammar.FunctionModifiersParses input.declarativeRemainder
      modifiers next.declarativeRemainder := by
  unfold functionModifiers at result
  rcases bind_ok_components_variant result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨payableMarker, afterPayable, payableResult, finished⟩
  have publicGrammar := optionalFunctionModifier_success_sound .publicKw
    publicResult
  have payableGrammar := optionalFunctionModifier_success_sound .payableKw
    payableResult
  cases location <;> cases publicMarker <;> cases payableMarker <;>
    cases finished <;>
    exact ⟨afterPublic.declarativeRemainder, publicGrammar,
      by simpa only [State.declarativeRemainder, State.emit]
        using payableGrammar⟩

/-- Function-modifier grammar soundness composes with source validity. -/
theorem functionModifiers_success_sound_and_validFor
    (location : FunctionLocation) {input next : State}
    {modifiers : FunctionModifiers} (inputValid : input.ValidFor)
    (result : functionModifiers location input = .ok modifiers next) :
    DeclarativeGrammar.FunctionModifiersParses input.declarativeRemainder
        modifiers next.declarativeRemainder ∧
      FunctionModifiers.ValidFor input.file modifiers := by
  refine ⟨functionModifiers_success_sound location result, ?_⟩
  have valid := functionModifiers_validFor location input inputValid
  rw [result] at valid
  exact valid.1

/-- Diagnostic-free module modifier success contains no contract marker. -/
theorem functionModifiers_module_success_allowed {input next : State}
    {modifiers : FunctionModifiers} (diagnosticFree : next.diagnosticsRev = [])
    (result : functionModifiers .module input = .ok modifiers next) :
    DeclarativeGrammar.ModuleFunctionModifiersAllowed modifiers := by
  unfold functionModifiers at result
  rcases bind_ok_components_variant result with
    ⟨publicMarker, afterPublic, publicResult, rest⟩
  rcases bind_ok_components_variant rest with
    ⟨payableMarker, afterPayable, payableResult, finished⟩
  cases publicMarker with
  | none =>
      cases payableMarker with
      | none =>
          cases finished
          exact ⟨rfl, rfl⟩
      | some payableSpan =>
          cases finished
          simp [State.emit] at diagnosticFree
  | some publicSpan =>
      cases payableMarker <;> cases finished <;>
        simp [State.emit] at diagnosticFree

/-- Every contract modifier success satisfies the contract location policy. -/
theorem functionModifiers_contract_success_allowed {input next : State}
    {modifiers : FunctionModifiers}
    (_result : functionModifiers .contract input = .ok modifiers next) :
    DeclarativeGrammar.ContractFunctionModifiersAllowed modifiers := by
  trivial

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ReturnClauseSoundnessProperties
/-! Success soundness for optional function return clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional return clauses preserve marker priority, delimiters, and types. -/
theorem returnClause_success_sound {input next : State}
    {clause : Option ReturnClause}
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.OptionalReturnClauseParses input.declarativeRemainder
      clause next.declarativeRemainder := by
  unfold returnClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .returns
  · simp only [present, if_true] at result
    cases markerResult : contextual .returns .typeExpr input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases typesResult : delimited .leftParen .rightParen true typeExpr
            .typeExpr .typeExpr afterMarker with
        | invariant error => simp [typesResult] at result
        | reject failure rejected => simp [typesResult] at result
        | ok types afterTypes =>
            have typesGrammar := delimited_allowEmpty_trailing_success_sound
              .leftParen .rightParen typeExpr
              DeclarativeGrammar.TypeExprParses .typeExpr .typeExpr
              typeExpr_success_sound typeExpr_preservesTokenWindow typesResult
            simp only [typesResult, pure] at result
            cases result
            exact .present marker.span
              (contextual_success_exactTokenParses .returns .typeExpr
                markerResult) typesGrammar
  · have absent : isContextual input .returns = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .returns absent)

/-- Return-clause grammar soundness composes with source validity. -/
theorem returnClause_success_sound_and_validFor {input next : State}
    {clause : Option ReturnClause} (inputValid : input.ValidFor)
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.OptionalReturnClauseParses input.declarativeRemainder
        clause next.declarativeRemainder ∧
      Option.ValidFor ReturnClause.ValidFor input.file clause := by
  refine ⟨returnClause_success_sound result, ?_⟩
  have valid := returnClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.GenericParametersSoundnessProperties
/-! Success soundness for shared generic-parameter syntax. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Requiring nonempty generic parameters preserves span, state, and order. -/
theorem requireGenericParameters_success_shape
    {values : DelimitedList Identifier}
    {input next : State} {parameters : GenericParameters}
    (result : requireGenericParameters values input = .ok parameters next) :
    next = input ∧ parameters.span = values.span ∧
      parameters.elements.toList = values.elements := by
  unfold requireGenericParameters at result
  cases elements : values.elements with
  | nil => rw [elements] at result; contradiction
  | cons head tail =>
      rw [elements] at result
      cases result
      exact ⟨rfl, rfl, by simp [NonemptyList.toList]⟩

/-- Every successful generic parameter list follows its exact grammar. -/
theorem genericParameters_success_sound {input next : State}
    {parameters : GenericParameters}
    (result : genericParameters input = .ok parameters next) :
    DeclarativeGrammar.GenericParametersParses input.declarativeRemainder
      parameters next.declarativeRemainder := by
  unfold genericParameters at result
  cases valuesResult : delimited .less .greater false
      (identifier .parameter) .parameter .topLevel input with
  | invariant error =>
      simp [bind, valuesResult] at result
  | reject failure rejected =>
      simp [bind, valuesResult] at result
  | ok values afterValues =>
      have valuesGrammar := delimited_nonempty_trailing_success_sound
        .less .greater (identifier .parameter)
        DeclarativeGrammar.IdentifierParses .parameter .topLevel
        (identifier_success_sound .parameter)
        (identifier_preservesTokenWindow .parameter) valuesResult
      simp only [bind, valuesResult] at result
      have shape := requireGenericParameters_success_shape result
      rw [shape.1]
      unfold DeclarativeGrammar.GenericParametersParses
      simpa only [shape.2.1, shape.2.2] using valuesGrammar

/-- Generic-parameter grammar soundness composes with source validity. -/
theorem genericParameters_success_sound_and_validFor {input next : State}
    {parameters : GenericParameters} (inputValid : input.ValidFor)
    (result : genericParameters input = .ok parameters next) :
    DeclarativeGrammar.GenericParametersParses input.declarativeRemainder
        parameters next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Located.ValidFor input.file
        parameters := by
  refine ⟨genericParameters_success_sound result, ?_⟩
  have valid := genericParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Optional generic parameters preserve their leading-`<` branch priority. -/
theorem optionalGenericParameters_success_sound {input next : State}
    {parameters : Option GenericParameters}
    (result : optionalGenericParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalGenericParametersParses
      input.declarativeRemainder parameters next.declarativeRemainder := by
  unfold optionalGenericParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .less
  · simp only [present, if_true] at result
    cases parametersResult : genericParameters input with
    | invariant error => simp [parametersResult] at result
    | reject failure rejected => simp [parametersResult] at result
    | ok values afterValues =>
        simp only [parametersResult, pure] at result
        cases result
        exact .present (genericParameters_success_sound parametersResult)
  · have absent : isSymbol input .less = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .less absent)

/-- Optional generic grammar soundness composes with source validity. -/
theorem optionalGenericParameters_success_sound_and_validFor
    {input next : State} {parameters : Option GenericParameters}
    (inputValid : input.ValidFor)
    (result : optionalGenericParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalGenericParametersParses
        input.declarativeRemainder parameters next.declarativeRemainder ∧
      Option.ValidFor
        (NonemptyDelimitedList.ValidFor Located.ValidFor)
        input.file parameters := by
  refine ⟨optionalGenericParameters_success_sound result, ?_⟩
  have valid := optionalGenericParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParametersSoundnessProperties
/-! Diagnostic-free success soundness for named function-parameter lists. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free parameter-list success follows the strict grammar. -/
theorem functionParameters_success_sound {input next : State}
    {values : DelimitedList FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok values next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
      values next.declarativeRemainder := by
  unfold functionParameters at result
  unfold DeclarativeGrammar.FunctionParametersParses
  exact delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
    .leftParen .rightParen namedParameter
    DeclarativeGrammar.FunctionParameterParses .parameter .topLevel
    namedParameter_success_sound namedParameter_reflectsDiagnosticFreeOnSuccess
    namedParameter_preservesTokenWindow diagnosticFree result

/-- Strict parameter-list grammar soundness composes with source validity. -/
theorem functionParameters_success_sound_and_validFor {input next : State}
    {values : DelimitedList FunctionParameter} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : functionParameters input = .ok values next) :
    DeclarativeGrammar.FunctionParametersParses input.declarativeRemainder
        values next.declarativeRemainder ∧
      DelimitedList.ValidFor FunctionParameter.ValidFor input.file values := by
  refine ⟨functionParameters_success_sound diagnosticFree result, ?_⟩
  have valid := functionParameters_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaParameterBoundaryOutcomeSoundnessProperties
/-! Executable reflection of the public parameter recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A true executable public-boundary guard gives its exact stop. -/
theorem lambdaParameterBoundaryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = true) :
    DeclarativeGrammar.LambdaParameterBoundaryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · rcases tokenAt_of_isSymbol_eq_true .comma comma with
        ⟨span, token⟩
      exact .comma token
    · have commaFalse := Bool.eq_false_iff.mpr comma
      have rightParen : isSymbol input .rightParen = true := by
        simpa [atEndFalse, commaFalse] using boundary
      rcases tokenAt_of_isSymbol_eq_true .rightParen rightParen with
        ⟨span, token⟩
      exact .rightParen token

/-- A false executable guard excludes every public parameter boundary. -/
theorem no_lambdaParameterBoundaryStops_of_guard_eq_false
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = false) :
    ¬ DeclarativeGrammar.LambdaParameterBoundaryStops
      input.declarativeRemainder := by
  intro stops
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundary
  | comma present =>
      have comma : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [comma] at boundary
  | rightParen present =>
      have rightParen : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [rightParen] at boundary

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FunctionParameterBoundaryOutcomeSoundnessProperties
/-! Executable reflection of the public function-parameter recovery boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A true executable guard gives its exact public recovery boundary. -/
theorem functionParameterBoundaryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = true) :
    DeclarativeGrammar.FunctionParameterBoundaryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    by_cases comma : isSymbol input .comma = true
    · rcases tokenAt_of_isSymbol_eq_true .comma comma with
        ⟨span, token⟩
      exact .comma token
    · have commaFalse := Bool.eq_false_iff.mpr comma
      have rightParen : isSymbol input .rightParen = true := by
        simpa [atEndFalse, commaFalse] using boundary
      rcases tokenAt_of_isSymbol_eq_true .rightParen rightParen with
        ⟨span, token⟩
      exact .rightParen token

/-- A false executable guard excludes every public recovery boundary. -/
theorem no_functionParameterBoundaryStops_of_guard_eq_false
    (input : State)
    (boundary : (input.atEnd || isSymbol input .comma ||
      isSymbol input .rightParen) = false) :
    ¬ DeclarativeGrammar.FunctionParameterBoundaryStops
      input.declarativeRemainder := by
  intro stops
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundary
  | comma present =>
      have comma : isSymbol input .comma = true :=
        isSymbol_eq_true_of_tokenAt .comma (by
          simpa [State.declarativeRemainder] using present)
      simp [comma] at boundary
  | rightParen present =>
      have rightParen : isSymbol input .rightParen = true :=
        isSymbol_eq_true_of_tokenAt .rightParen (by
          simpa [State.declarativeRemainder] using present)
      simp [rightParen] at boundary

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LiteralProperties
/-! Compositional contracts for canonical literal token consumers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Core-literal success advances only the parser cursor. -/
theorem coreLiteral_ok_state_shape {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals rfl

/-- Boolean-identifier success advances only the parser cursor. -/
theorem booleanIdentifier_ok_state_shape {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals rfl

/-- Core literals preserve the complete token window on every reply. -/
theorem coreLiteral_preservesTokenWindow :
    Parser.PreservesTokenWindow coreLiteral := by
  intro input
  unfold coreLiteral
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      all_goals exact ⟨rfl, rfl⟩

/-- Boolean builtin names preserve the complete token window on every reply. -/
theorem booleanIdentifier_preservesTokenWindow :
    Parser.PreservesTokenWindow booleanIdentifier := by
  intro input
  unfold booleanIdentifier
  cases found : input.peek? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind
      all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
      case keyword keyword =>
        cases keyword
        all_goals try { exact rejectAt_preservesTokenWindow input _ _ }
        all_goals exact ⟨rfl, rfl⟩

/-- Core-literal success preserves the immutable token carrier. -/
theorem coreLiteral_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess coreLiteral := by
  intro input literal next result
  rw [coreLiteral_ok_state_shape result]

/-- Core-literal success consumes exactly one token. -/
theorem coreLiteral_cursor_lt_onSuccess {input next : State}
    {literal : CoreLiteral}
    (result : coreLiteral input = .ok literal next) :
    input.cursor < next.cursor := by
  rw [coreLiteral_ok_state_shape result]
  simp

/-- Core-literal success advances by exactly one token. -/
theorem coreLiteral_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess coreLiteral := by
  intro input literal next result
  rw [coreLiteral_ok_state_shape result]
  simp

/-- A core literal starts at the literal token it consumes. -/
theorem coreLiteral_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess coreLiteral (·.span) := by
  intro input literal next result
  unfold coreLiteral at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals exact ⟨_, rfl, rfl⟩

/-- Boolean-identifier success preserves the immutable token carrier. -/
theorem booleanIdentifier_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess booleanIdentifier := by
  intro input name next result
  rw [booleanIdentifier_ok_state_shape result]

/-- Boolean-identifier success consumes exactly one token. -/
theorem booleanIdentifier_cursor_lt_onSuccess {input next : State}
    {name : Identifier}
    (result : booleanIdentifier input = .ok name next) :
    input.cursor < next.cursor := by
  rw [booleanIdentifier_ok_state_shape result]
  simp

/-- Boolean-identifier success advances by exactly one token. -/
theorem booleanIdentifier_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess booleanIdentifier := by
  intro input name next result
  rw [booleanIdentifier_ok_state_shape result]
  simp

/-- A Boolean builtin name starts at its keyword token. -/
theorem booleanIdentifier_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess booleanIdentifier (·.span) := by
  intro input name next result
  unfold booleanIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact ⟨_, rfl, rfl⟩

end Solcore.Syntax.Parser
end
