import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Type

/-! Diagnostic-free reflection for recursive type-expression parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open QualifiedNameInternals

private theorem qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next parsed diagnosticFree
      simp [qualifiedNameTail] at parsed
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next parsed diagnosticFree
      unfold qualifiedNameTail at parsed
      split at parsed
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at parsed
            | reject failure rejected => simp [componentResult] at parsed
            | ok component afterComponent =>
                simp only [componentResult] at parsed
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next parsed
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess context afterDot
                    component afterComponent componentResult afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot context input
                  dot afterDot dotResult afterDotFree
      · unfold finishQualifiedName at parsed
        cases parsed
        exact diagnosticFree

private theorem qualifiedName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (qualifiedName context phase) := by
  intro input value next parsed diagnosticFree
  unfold qualifiedName at parsed
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at parsed
  | reject failure rejected => simp [firstResult] at parsed
  | ok first afterFirst =>
      simp only [firstResult] at parsed
      have afterFirstFree :=
        qualifiedNameTail_reflectsDiagnosticFreeOnSuccess context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst value next parsed
            diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess context input first
        afterFirst firstResult afterFirstFree

private theorem requireNonempty_reflectsDiagnosticFreeOnSuccess
    {alpha : Type} (parsed : DelimitedList alpha) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (requireNonempty parsed phase) := by
  unfold requireNonempty
  cases parsed.elements with
  | nil =>
      intro input value next result diagnosticFree
      contradiction
  | cons head tail =>
      exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseNamedTypeArguments_reflectsDiagnosticFreeOnSuccess
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
    intro parsed
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (requireNonempty_reflectsDiagnosticFreeOnSuccess parsed .typeExpr)
    intro nonempty
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem finishNamedType_reflectsDiagnosticFreeOnSuccess
    (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishNamedType name arguments) := by
  unfold finishNamedType
  dsimp only
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseNamedType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseNamedType nested) := by
  unfold parseNamedType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (qualifiedName_reflectsDiagnosticFreeOnSuccess .typeExpr .typeExpr)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseNamedTypeArguments_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro arguments
  exact finishNamedType_reflectsDiagnosticFreeOnSuccess name arguments

private theorem parseMappingType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseMappingType nested) := by
  unfold parseMappingType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .mapping .typeExpr)
  intro mapping
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftParen .typeExpr)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro key
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .fatArrow .typeExpr)
  intro arrow
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro value
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightParen .typeExpr)
  intro closing
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseComptimeType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseComptimeType nested) := by
  unfold parseComptimeType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .comptime .typeExpr)
  intro comptime
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .less .typeExpr)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess nestedReflects
  intro inner
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .greater .typeExpr)
  intro closing
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseProxyType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseProxyType nested) := by
  intro input value next parsed diagnosticFree
  unfold parseProxyType at parsed
  cases markerResult : symbol .at .typeExpr input with
  | invariant error => simp [markerResult] at parsed
  | reject failure rejected => simp [markerResult] at parsed
  | ok marker afterMarker =>
      simp only [markerResult] at parsed
      cases innerResult : nested afterMarker with
      | invariant error => simp [innerResult] at parsed
      | reject failure rejected => simp [innerResult] at parsed
      | ok inner afterInner =>
          simp only [innerResult] at parsed
          cases parsed
          have afterMarkerFree := nestedReflects afterMarker inner next
            innerResult diagnosticFree
          exact symbol_reflectsDiagnosticFreeOnSuccess .at .typeExpr input
            marker afterMarker markerResult afterMarkerFree

private theorem parseTupleType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseTupleType nested) := by
  unfold parseTupleType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedReflects)
  intro tuple
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

private theorem parseFunctionReturns_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (TypeFunctionInternals.parseFunctionReturns nested) := by
  unfold TypeFunctionInternals.parseFunctionReturns
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    getState_reflectsDiagnosticFreeOnSuccess
  intro state
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (contextual_reflectsDiagnosticFreeOnSuccess .returns .typeExpr)
    intro returnsKeyword
    apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
        nested .typeExpr .typeExpr nestedReflects)
    intro values
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess none

private theorem parseFunctionType_reflectsDiagnosticFreeOnSuccess
    (nested : Parser TypeExpr)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested) :
    Parser.ReflectsDiagnosticFreeOnSuccess (parseFunctionType nested) := by
  unfold parseFunctionType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .functionKw .typeExpr)
  intro functionKeyword
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      nested .typeExpr .typeExpr nestedReflects)
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (parseFunctionReturns_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects)
  intro returns
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- A diagnostic-free successful bounded type parse had a diagnostic-free input. -/
theorem typeExprWithFuel_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel,
      Parser.ReflectsDiagnosticFreeOnSuccess (typeExprWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input value next parsed diagnosticFree
      simp [typeExprWithFuel] at parsed
  | succ fuel inductionHypothesis =>
      intro input value next parsed diagnosticFree
      simp only [typeExprWithFuel] at parsed
      split at parsed
      · exact parseFunctionType_reflectsDiagnosticFreeOnSuccess
          (typeExprWithFuel fuel) inductionHypothesis input value next parsed
            diagnosticFree
      · split at parsed
        · exact parseComptimeType_reflectsDiagnosticFreeOnSuccess
            (typeExprWithFuel fuel) inductionHypothesis input value next parsed
              diagnosticFree
        · split at parsed
          · exact parseMappingType_reflectsDiagnosticFreeOnSuccess
              (typeExprWithFuel fuel) inductionHypothesis input value next parsed
                diagnosticFree
          · split at parsed
            · exact parseProxyType_reflectsDiagnosticFreeOnSuccess
                (typeExprWithFuel fuel) inductionHypothesis input value next
                  parsed diagnosticFree
            · split at parsed
              · exact parseTupleType_reflectsDiagnosticFreeOnSuccess
                  (typeExprWithFuel fuel) inductionHypothesis input value next
                    parsed diagnosticFree
              · split at parsed
                · exact parseNamedType_reflectsDiagnosticFreeOnSuccess
                    (typeExprWithFuel fuel) inductionHypothesis input value next
                      parsed diagnosticFree
                · unfold rejectAt at parsed
                  contradiction

/-- A diagnostic-free successful public type parse had a diagnostic-free input. -/
theorem typeExpr_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess typeExpr := by
  intro input value next parsed diagnosticFree
  unfold typeExpr at parsed
  exact typeExprWithFuel_reflectsDiagnosticFreeOnSuccess
    (input.remainingCount + 1) input value next parsed diagnosticFree

end Solcore.Syntax.Parser
