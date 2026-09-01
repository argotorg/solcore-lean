import Solcore.Syntax.DeclarativeCoreLambdaGrammar
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Expression.Atom
import Solcore.Syntax.Parser.ParameterRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

/-!
Diagnostic reflection for Core lambda parameters and their optional return
type suffix.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace LambdaParameterInternals

private theorem finishTypedParameter_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (FunctionParameterInternals.finishTypedParameter start marker name
        type) := by
  unfold FunctionParameterInternals.finishTypedParameter
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
      (FunctionParameterInternals.errorParameter span constraint) := by
  unfold FunctionParameterInternals.errorParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
  intro emitted
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem namedParameterTail_reflectsDiagnosticFreeOnSuccess
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (FunctionParameterInternals.namedParameterTail start marker name
        errorSpan) := by
  unfold FunctionParameterInternals.namedParameterTail
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .colon .parameter)
    intro colon
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      typeExpr_reflectsDiagnosticFreeOnSuccess
    intro type
    exact finishTypedParameter_reflectsDiagnosticFreeOnSuccess start marker
      name type
  · exact errorParameter_reflectsDiagnosticFreeOnSuccess errorSpan
      .namedParameterRequiresType

/-- The ordinary inferred-or-typed suffix never removes diagnostics. -/
theorem ordinaryLambdaParameterTail_reflectsDiagnosticFreeOnSuccess
    (name : Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (ordinaryLambdaParameterTail name) := by
  unfold ordinaryLambdaParameterTail
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (namedParameterTail_reflectsDiagnosticFreeOnSuccess name.span none name
        name.span)
    intro parameter
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem ordinaryLambdaParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess ordinaryLambdaParameter := by
  unfold ordinaryLambdaParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .parameter)
  intro name
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact ordinaryLambdaParameterTail_reflectsDiagnosticFreeOnSuccess name
  · exact ordinaryLambdaParameterTail_reflectsDiagnosticFreeOnSuccess name

private theorem comptimeLambdaParameterTail_reflectsDiagnosticFreeOnSuccess
    (marker : Token) (name : Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (comptimeLambdaParameterTail marker name) := by
  unfold comptimeLambdaParameterTail
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (namedParameterTail_reflectsDiagnosticFreeOnSuccess marker.span
        (some marker.span) name (SourceSpan.cover marker.span name.span))
    intro parameter
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (errorParameter_reflectsDiagnosticFreeOnSuccess
        (SourceSpan.cover marker.span name.span)
        .comptimeParameterRequiresType)
    intro parameter
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem comptimeLambdaParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess comptimeLambdaParameter := by
  unfold comptimeLambdaParameter
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .comptime .parameter)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (identifier_reflectsDiagnosticFreeOnSuccess .parameter)
  intro name
  exact comptimeLambdaParameterTail_reflectsDiagnosticFreeOnSuccess marker name

/-- The non-recovering ordered lambda-parameter core reflects diagnostic
freedom through whichever exact branch it selects. -/
theorem lambdaParameterCore_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess lambdaParameterCore := by
  intro input value next parsed diagnosticFree
  unfold lambdaParameterCore at parsed
  split at parsed
  · simp only [Bool.and_true] at parsed
    split at parsed
    · exact comptimeLambdaParameter_reflectsDiagnosticFreeOnSuccess input
        value next parsed diagnosticFree
    · exact ordinaryLambdaParameter_reflectsDiagnosticFreeOnSuccess input
        value next parsed diagnosticFree
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at parsed
    exact ordinaryLambdaParameter_reflectsDiagnosticFreeOnSuccess input value
      next parsed diagnosticFree

private theorem recoverLambdaParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess recoverLambdaParameter := by
  intro input value next recovered diagnosticFree
  unfold recoverLambdaParameter at recovered
  cases recoveryResult : FunctionParameterInternals.recoverParameter input with
  | ok parameter afterRecovery =>
      simp only [recoveryResult] at recovered
      cases recovered
      exact False.elim
        (FunctionParameterInternals.recoverParameter_diagnostics_ne_nil_onSuccess
          recoveryResult diagnosticFree)
  | reject failure rejected => simp [recoveryResult] at recovered
  | invariant error => simp [recoveryResult] at recovered

end LambdaParameterInternals

/-- A diagnostic-free successful lambda-parameter parse had a diagnostic-free
input. -/
theorem lambdaParameter_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess lambdaParameter := by
  intro input value next parsed diagnosticFree
  unfold lambdaParameter at parsed
  cases coreResult : LambdaParameterInternals.lambdaParameterCore input with
  | ok parameter afterCore =>
      simp only [coreResult] at parsed
      cases parsed
      exact
        LambdaParameterInternals.lambdaParameterCore_reflectsDiagnosticFreeOnSuccess
          input value next coreResult diagnosticFree
  | reject failure failedState =>
      simp only [coreResult] at parsed
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then .reject failure rewound
        else LambdaParameterInternals.recoverLambdaParameter
          (rewound.emit failure.toDiagnostic)) = .ok value next at parsed
      split at parsed
      · contradiction
      · have emittedFree :=
          LambdaParameterInternals.recoverLambdaParameter_reflectsDiagnosticFreeOnSuccess
            (rewound.emit failure.toDiagnostic) value next parsed diagnosticFree
        simp [State.emit] at emittedFree
  | invariant error => simp [coreResult] at parsed

namespace ExpressionAtomInternals

/-- Optional lambda return types reflect through their arrow and recursive type
parse. -/
theorem optionalLambdaReturnType_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess optionalLambdaReturnType := by
  unfold optionalLambdaReturnType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro observed
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (symbol_reflectsDiagnosticFreeOnSuccess .arrow .typeExpr)
    intro arrow
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      typeExpr_reflectsDiagnosticFreeOnSuccess
    intro type
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end ExpressionAtomInternals

end Solcore.Syntax.Parser
