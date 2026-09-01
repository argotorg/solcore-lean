import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.ModulePath
import Solcore.Syntax.Parser.Operator

/-! Diagnostic-freedom reflection for shared name and selector parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

private theorem qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input value next result diagnosticFree
      simp [qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input value next result diagnosticFree
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent value next result
                    diagnosticFree
                have afterDotFree :=
                  identifier_reflectsDiagnosticFreeOnSuccess context afterDot
                    component afterComponent componentResult afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot context input
                  dot afterDot dotResult afterDotFree
      · unfold finishQualifiedName at result
        cases result
        exact diagnosticFree

end QualifiedNameInternals

/-- Qualified-name parsing cannot erase an incoming diagnostic. -/
theorem qualifiedName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.ReflectsDiagnosticFreeOnSuccess (qualifiedName context phase) := by
  intro input value next result diagnosticFree
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree :=
        QualifiedNameInternals.qualifiedNameTail_reflectsDiagnosticFreeOnSuccess
          context phase first (afterFirst.remainingCount + 1) first []
            afterFirst value next result diagnosticFree
      exact identifier_reflectsDiagnosticFreeOnSuccess context input first
        afterFirst firstResult afterFirstFree

/-- Module-path parsing cannot erase an incoming diagnostic. -/
theorem modulePath_reflectsDiagnosticFreeOnSuccess (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (modulePath context) := by
  intro input value next result diagnosticFree
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name afterName =>
            simp only [nameResult] at result
            cases result
            have afterMarkerFree :=
              qualifiedName_reflectsDiagnosticFreeOnSuccess context .topLevel
                afterMarker name next nameResult diagnosticFree
            exact symbol_reflectsDiagnosticFreeOnSuccess .at context input
              marker afterMarker markerResult afterMarkerFree
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_reflectsDiagnosticFreeOnSuccess context .topLevel
          input name next nameResult diagnosticFree

namespace OperatorInternals

private theorem operatorParts_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) : ∀ fuel partsRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (operatorParts context fuel partsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input value next result diagnosticFree
      simp [operatorParts] at result
  | succ fuel inductionHypothesis =>
      intro partsRev input value next result diagnosticFree
      unfold operatorParts at result
      cases found : input.peek? with
      | some token =>
          simp only [found] at result
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only [part] at result
              exact inductionHypothesis (spelling :: partsRev)
                { input with cursor := input.cursor + 1 } value next result
                  diagnosticFree
          | none =>
              simp only [part] at result
              split at result
              · simp [rejectAt] at result
              · cases result
                exact diagnosticFree
      | none =>
          simp only [found] at result
          split at result
          · simp [rejectAt] at result
          · cases result
            exact diagnosticFree

end OperatorInternals

/-- Parenthesized operator parsing cannot erase an incoming diagnostic. -/
theorem operatorSelector_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (operatorSelector context) := by
  intro input value next result diagnosticFree
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      simp only [openingResult] at result
      cases partsResult : OperatorInternals.operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing afterClosing =>
              simp only [closingResult] at result
              cases result
              have afterPartsFree :=
                symbol_reflectsDiagnosticFreeOnSuccess .rightParen context
                  afterParts closing next closingResult diagnosticFree
              have afterOpeningFree :=
                OperatorInternals.operatorParts_reflectsDiagnosticFreeOnSuccess
                  context (afterOpening.remainingCount + 1) [] afterOpening
                    parts afterParts partsResult afterPartsFree
              exact symbol_reflectsDiagnosticFreeOnSuccess .leftParen context
                input opening afterOpening openingResult afterOpeningFree

/-- Selector-name parsing cannot erase an incoming diagnostic. -/
theorem selectorName_reflectsDiagnosticFreeOnSuccess
    (context : ParseContext) :
    Parser.ReflectsDiagnosticFreeOnSuccess (selectorName context) := by
  intro input value next result diagnosticFree
  unfold selectorName at result
  split at result
  · exact operatorSelector_reflectsDiagnosticFreeOnSuccess context input
      value next result diagnosticFree
  · cases nameResult : identifier context input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        simp only [nameResult] at result
        cases result
        exact identifier_reflectsDiagnosticFreeOnSuccess context input name
          next nameResult diagnosticFree

end Solcore.Syntax.Parser
