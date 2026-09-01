import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Pragma

/-! Diagnostic-freedom reflection for provisional pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTail_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel itemsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess (pragmaItemsTail fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input value next result diagnosticFree
      simp [pragmaItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input value next result diagnosticFree
      unfold pragmaItemsTail at result
      split at result
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            split at result
            · cases result
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma .pragmaDecl
                input comma next commaResult diagnosticFree
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  simp only [itemResult] at result
                  have afterItemFree := inductionHypothesis (item :: itemsRev)
                    afterItem value next result diagnosticFree
                  have afterCommaFree :=
                    identifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl
                      afterComma item afterItem itemResult afterItemFree
                  exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                    .pragmaDecl input comma afterComma commaResult
                      afterCommaFree
      · cases result
        exact diagnosticFree

private theorem pragmaItems_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess pragmaItems := by
  intro input value next result diagnosticFree
  unfold pragmaItems at result
  split at result
  · cases result
    exact diagnosticFree
  · cases itemResult : identifier .pragmaDecl input with
    | invariant error => simp [itemResult] at result
    | reject failure rejected => simp [itemResult] at result
    | ok item afterItem =>
        simp only [itemResult] at result
        have afterItemFree := pragmaItemsTail_reflectsDiagnosticFreeOnSuccess
          (afterItem.remainingCount + 1) [item] afterItem value next result
            diagnosticFree
        exact identifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl input
          item afterItem itemResult afterItemFree

end Solcore.Syntax.Parser.PragmaInternals

namespace Solcore.Syntax.Parser

/-- Pragma parsing cannot erase an incoming diagnostic. -/
theorem pragmaDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess pragmaDecl := by
  unfold pragmaDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .pragmaKw .pragmaDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (rawIdentifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    PragmaInternals.pragmaItems_reflectsDiagnosticFreeOnSuccess
  intro items
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .pragmaDecl)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
