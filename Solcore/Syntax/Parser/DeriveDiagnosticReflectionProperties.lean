import Solcore.Syntax.Parser.DeriveRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.DiagnosticReflectionProperties

/-! Backward diagnostic reflection for derive targets and attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace DeriveTargetInternals

/-- A derive component either parses an identifier or adds a retained diagnostic. -/
theorem deriveComponent_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveComponent := by
  intro input name next result diagnosticFree
  unfold deriveComponent at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      simp only [found] at result
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved] at result
          exact identifier_reflectsDiagnosticFreeOnSuccess .topItem input name
            next result diagnosticFree
      | some keywordValue =>
          simp only [reserved] at result
          cases result
          simp [State.emit] at diagnosticFree

private theorem finishDeriveTarget_reflectsDiagnosticFreeOnSuccess
    (first last : Identifier) (tailRev : List Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishDeriveTarget first last tailRev) := by
  intro input target next result diagnosticFree
  unfold finishDeriveTarget at result
  cases result
  exact diagnosticFree

private theorem deriveTargetTail_reflectsDiagnosticFreeOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (deriveTargetTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input target next result diagnosticFree
      simp [deriveTargetTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input target next result diagnosticFree
      unfold deriveTargetTail at result
      split at result
      · cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent target next result
                    diagnosticFree
                have afterDotFree :=
                  deriveComponent_reflectsDiagnosticFreeOnSuccess afterDot
                    component afterComponent componentResult
                      afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot .topItem
                  input dot afterDot dotResult afterDotFree
      · exact finishDeriveTarget_reflectsDiagnosticFreeOnSuccess first last
          tailRev input target next result diagnosticFree

end DeriveTargetInternals

/-- Complete dotted derive targets cannot erase incoming diagnostics. -/
theorem deriveTarget_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveTarget := by
  intro input target next result diagnosticFree
  unfold deriveTarget at result
  cases firstResult : DeriveTargetInternals.deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree :=
        DeriveTargetInternals.deriveTargetTail_reflectsDiagnosticFreeOnSuccess
          first (afterFirst.remainingCount + 1) first [] afterFirst target next
            result diagnosticFree
      exact
        DeriveTargetInternals.deriveComponent_reflectsDiagnosticFreeOnSuccess
          input first afterFirst firstResult afterFirstFree

namespace DeriveAttributeInternals

/-- The normal derive-attribute path cannot erase incoming diagnostics. -/
theorem valid_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess valid := by
  unfold valid
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .hash .topItem)
  intro hash
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftBracket .topItem)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .derive .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
      .leftParen .rightParen true deriveTarget .topItem .topLevel
      deriveTarget_reflectsDiagnosticFreeOnSuccess)
  intro targets
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBracket .topItem)
  intro closing
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Recovery successes are always diagnosed, so reflection holds vacuously. -/
theorem recovered_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess recovered := by
  intro input value next result diagnosticFree
  exact False.elim (deriveRecovered_success_hasDiagnostic result diagnosticFree)

end DeriveAttributeInternals

/-- Public derive-attribute parsing cannot erase incoming diagnostics. -/
theorem deriveAttribute_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveAttribute := by
  unfold deriveAttribute
  exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
    DeriveAttributeInternals.valid_reflectsDiagnosticFreeOnSuccess
    DeriveAttributeInternals.recovered_reflectsDiagnosticFreeOnSuccess

end Solcore.Syntax.Parser
