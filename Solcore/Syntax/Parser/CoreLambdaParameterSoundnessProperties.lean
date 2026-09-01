import Solcore.Syntax.Parser.CoreLambdaParameterDiagnosticReflectionProperties
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-!
Exact diagnostic-free declarative soundness for Core lambda parameters.
-/

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

private theorem comptimeLambdaParameterAbsent_of_core_false
    {input : State}
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

private theorem finishTypedParameter_success_sound
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) {input next : State} {value : FunctionParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.finishTypedParameter start marker
      name type input = .ok value next) :
    DeclarativeGrammar.ParameterTypeAllowed type ∧
      value = {
        span := SourceSpan.cover start type.span
        value := .typed marker name type
      } ∧ next = input := by
  unfold FunctionParameterInternals.finishTypedParameter at result
  cases typeValue : type.value
  all_goals
    simp only [typeValue, emitDiagnostic, modifyState, bind, pure] at result
  all_goals cases result
  all_goals try { simp [State.emit] at diagnosticFree }
  all_goals simp [DeclarativeGrammar.ParameterTypeAllowed, typeValue]

private theorem namedParameterTail_success_sound
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input next : State}
    {value : FunctionParameter} (diagnosticFree : next.diagnosticsRev = [])
    (result : FunctionParameterInternals.namedParameterTail start marker name
      errorSpan input = .ok value next) :
    ∃ colonSpan afterColon type,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      DeclarativeGrammar.TypeExprParses afterColon type
        next.declarativeRemainder ∧
      DeclarativeGrammar.ParameterTypeAllowed type ∧
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
    rcases finishTypedParameter_success_sound start marker name type
        diagnosticFree finished with ⟨typeAllowed, valueEq, nextEq⟩
    subst next
    exact ⟨colon.span, afterColon.declarativeRemainder, type,
      symbol_success_exactTokenParses .colon .parameter colonResult,
      typeExpr_success_sound typeResult, typeAllowed, valueEq⟩
  · simp only [typed, Bool.false_eq_true, if_false] at result
    exact False.elim
      (FunctionParameterInternals.errorParameter_diagnostics_ne_nil_onSuccess
        errorSpan .namedParameterRequiresType result diagnosticFree)

private theorem ordinaryLambdaParameterTail_success_sound
    (name : Identifier) {input next : State} {value : LambdaParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ordinaryLambdaParameterTail name input = .ok value next) :
    DeclarativeGrammar.OrdinaryLambdaParameterTailParses name
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold ordinaryLambdaParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨parameter, afterParameter, parameterResult, finished⟩
    cases finished
    rcases namedParameterTail_success_sound name.span none name name.span
        diagnosticFree parameterResult with
      ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, typeAllowed,
        parameterEq⟩
    subst parameter
    exact .typed colonSpan colonGrammar typeGrammar typeAllowed
  · have colonAbsent : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [colonAbsent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .inferred
      (symbolAbsentAt_of_isSymbol_eq_false .colon colonAbsent)

private theorem ordinaryLambdaParameter_success_sound
    {input next : State} {value : LambdaParameter}
    (comptimeAbsent :
      ¬ DeclarativeGrammar.ComptimeLambdaParameterStartsAt
        input.declarativeRemainder)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ordinaryLambdaParameter input = .ok value next) :
    DeclarativeGrammar.LambdaParameterParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold ordinaryLambdaParameter at result
  rcases bind_ok_components result with
    ⟨name, afterName, nameResult, rest⟩
  have nameGrammar := identifier_success_sound .parameter nameResult
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true, emitDiagnostic, modifyState, bind] at rest
    have emittedFree :=
      ordinaryLambdaParameterTail_reflectsDiagnosticFreeOnSuccess name
        (afterName.emit {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }) value next rest diagnosticFree
    simp [State.emit] at emittedFree
  · have warnedFalse :
        (name.value == ContextualKeyword.comptime.spelling) = false :=
      Bool.eq_false_iff.mpr warned
    simp only [warnedFalse, Bool.false_eq_true, if_false] at rest
    have tailGrammar := ordinaryLambdaParameterTail_success_sound name
      diagnosticFree rest
    exact .ordinary comptimeAbsent
      (.parsed nameGrammar (by exact fun equal => warned (beq_iff_eq.mpr equal))
        tailGrammar)

private theorem comptimeLambdaParameterTail_success_sound
    (marker : Token) (name : Identifier) {input next : State}
    {value : LambdaParameter} (diagnosticFree : next.diagnosticsRev = [])
    (result : comptimeLambdaParameterTail marker name input =
      .ok value next) :
    ∃ colonSpan afterColon type,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      DeclarativeGrammar.TypeExprParses afterColon type
        next.declarativeRemainder ∧
      DeclarativeGrammar.ParameterTypeAllowed type ∧
      value = {
        span := SourceSpan.cover marker.span type.span
        value := .typed (some marker.span) name type
      } := by
  unfold comptimeLambdaParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true] at result
    rcases bind_ok_components result with
      ⟨parameter, afterParameter, parameterResult, finished⟩
    cases finished
    rcases namedParameterTail_success_sound marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) diagnosticFree parameterResult
      with ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, typeAllowed,
        parameterEq⟩
    subst parameter
    exact ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, typeAllowed,
      rfl⟩
  · simp only [typed, Bool.false_eq_true, if_false] at result
    cases parameterResult : FunctionParameterInternals.errorParameter
        (SourceSpan.cover marker.span name.span)
        .comptimeParameterRequiresType input with
    | ok parameter afterParameter =>
        simp only [parameterResult, pure] at result
        cases result
        exact False.elim
          (FunctionParameterInternals.errorParameter_diagnostics_ne_nil_onSuccess
            (SourceSpan.cover marker.span name.span)
            .comptimeParameterRequiresType parameterResult diagnosticFree)
    | reject failure rejected => simp [parameterResult] at result
    | invariant error => simp [parameterResult] at result

private theorem comptimeLambdaParameter_success_sound
    {input next : State} {value : LambdaParameter}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : comptimeLambdaParameter input = .ok value next) :
    DeclarativeGrammar.LambdaParameterParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold comptimeLambdaParameter at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, rest⟩
  rcases bind_ok_components rest with
    ⟨name, afterName, nameResult, tailResult⟩
  rcases comptimeLambdaParameterTail_success_sound marker name diagnosticFree
      tailResult with
    ⟨colonSpan, afterColon, type, colonGrammar, typeGrammar, typeAllowed,
      valueEq⟩
  subst value
  exact .comptime (.parsed marker.span colonSpan
    (contextual_success_exactTokenParses .comptime .parameter markerResult)
    (identifier_success_sound .parameter nameResult) colonGrammar typeGrammar
    typeAllowed)

/-- Every diagnostic-free success of the ordered non-recovering core follows
the exact lambda-parameter grammar. -/
theorem lambdaParameterCore_success_sound {input next : State}
    {value : LambdaParameter} (diagnosticFree : next.diagnosticsRev = [])
    (result : lambdaParameterCore input = .ok value next) :
    DeclarativeGrammar.LambdaParameterParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold lambdaParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeLambdaParameter_success_sound diagnosticFree result
    · exact ordinaryLambdaParameter_success_sound
        (comptimeLambdaParameterAbsent_of_core_false (by simp_all))
        diagnosticFree result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryLambdaParameter_success_sound
      (comptimeLambdaParameterAbsent_of_core_false (by simp_all))
      diagnosticFree result

end LambdaParameterInternals

/-- Every diagnostic-free public lambda-parameter success follows the strict
parser-independent grammar; recovery successes are excluded. -/
theorem lambdaParameter_success_sound {input next : State}
    {value : LambdaParameter} (diagnosticFree : next.diagnosticsRev = [])
    (result : lambdaParameter input = .ok value next) :
    DeclarativeGrammar.LambdaParameterParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold lambdaParameter at result
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter afterCore =>
      simp only [coreResult] at result
      cases result
      exact LambdaParameterInternals.lambdaParameterCore_success_sound
        diagnosticFree coreResult
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · unfold LambdaParameterInternals.recoverLambdaParameter at result
        cases recoveryResult : FunctionParameterInternals.recoverParameter
            (rewound.emit failure.toDiagnostic) with
        | ok recovered afterRecovery =>
            simp only [recoveryResult] at result
            cases result
            exact False.elim
              (FunctionParameterInternals.recoverParameter_diagnostics_ne_nil_onSuccess
                recoveryResult diagnosticFree)
        | reject recoveryFailure rejected => simp [recoveryResult] at result
        | invariant error => simp [recoveryResult] at result
  | invariant error => simp [coreResult] at result

end Solcore.Syntax.Parser
