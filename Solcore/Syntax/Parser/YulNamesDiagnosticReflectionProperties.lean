import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.YulExpressionLeafSoundnessProperties
import Solcore.Syntax.Parser.Yul.Common

/-! Diagnostic reflection for inline-Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Finishing a Yul name sequence is non-consuming and preserves diagnostics. -/
theorem finishYulNames_reflectsDiagnosticFreeOnSuccess
    (first last : YulIdentifier) (tailRev : List YulIdentifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishYulNames first last tailRev) := by
  intro input names next result diagnosticFree
  unfold finishYulNames at result
  cases result
  exact diagnosticFree

/-- Every successful comma-prioritized Yul name tail reflects diagnostic
freedom through its comma, following name, and recursive suffix. -/
theorem yulNamesTail_reflectsDiagnosticFreeOnSuccess
    (first : YulIdentifier) :
    ∀ fuel last tailRev,
      Parser.ReflectsDiagnosticFreeOnSuccess
        (yulNamesTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input names next result diagnosticFree
      simp [yulNamesTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input names next result diagnosticFree
      unfold yulNamesTail at result
      split at result
      · cases commaResult : symbol .comma .yulStatement input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            cases nameResult : yulName afterComma with
            | invariant error => simp [nameResult] at result
            | reject failure rejected => simp [nameResult] at result
            | ok name afterName =>
                simp only [nameResult] at result
                have afterNameFree := inductionHypothesis name
                  (name :: tailRev) afterName names next result diagnosticFree
                have afterCommaFree :=
                  yulName_reflectsDiagnosticFreeOnSuccess afterComma name
                    afterName nameResult afterNameFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                  .yulStatement input comma afterComma commaResult
                    afterCommaFree
      · exact finishYulNames_reflectsDiagnosticFreeOnSuccess first last
          tailRev input names next result diagnosticFree

/-- Public Yul name-sequence parsing reflects diagnostic freedom. -/
theorem yulNames_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess yulNames := by
  intro input names next result diagnosticFree
  unfold yulNames at result
  cases firstResult : yulName input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree := yulNamesTail_reflectsDiagnosticFreeOnSuccess first
        (afterFirst.remainingCount + 1) first [] afterFirst names next result
          diagnosticFree
      exact yulName_reflectsDiagnosticFreeOnSuccess input first afterFirst
        firstResult afterFirstFree

end Solcore.Syntax.Parser
