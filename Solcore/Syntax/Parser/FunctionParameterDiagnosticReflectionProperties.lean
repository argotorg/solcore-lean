import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ParameterRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.TypeDiagnosticReflectionProperties

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
