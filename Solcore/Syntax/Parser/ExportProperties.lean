import Solcore.Syntax.Parser.Export
import Solcore.Syntax.Parser.PrimitiveCarrierProperties

/-! Token-window and cursor contracts for canonical export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportPathTail_preservesTokenWindow (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold ExportInternals.exportPathTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot .exportDecl input
        cases dotResult : symbol .dot .exportDecl input with
        | invariant error =>
            simp only [Reply.PreservesTokenWindow]
        | reject failure rejected =>
            rw [dotResult] at dotShape
            simpa only [Reply.PreservesTokenWindow] using dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            simp only
            have componentShape :=
              identifier_preservesTokenWindow .exportDecl afterDot
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error =>
                simp only [Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simpa only [Reply.PreservesTokenWindow] using
                  componentShape.trans dotShape
            | ok component afterComponent =>
                rw [componentResult] at componentShape
                simpa only using (inductionHypothesis component
                    (component :: tailRev) afterComponent).trans
                  (componentShape.trans dotShape)
      · unfold ExportInternals.finishExportPath
        exact ⟨rfl, rfl⟩

/-- Export paths preserve their immutable token carrier and active window. -/
theorem exportPath_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportPath := by
  intro input
  unfold ExportInternals.exportPath
  have firstShape := identifier_preservesTokenWindow .exportDecl input
  cases firstResult : identifier .exportDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first afterFirst =>
      rw [firstResult] at firstShape
      exact (exportPathTail_preservesTokenWindow first
        (afterFirst.remainingCount + 1) first [] afterFirst).trans firstShape

/-- Successful export paths retain the immutable lexer token carrier. -/
theorem exportPath_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportPath :=
  exportPath_preservesTokenWindow.preservesTokensOnSuccess

private theorem exportPathTail_keepsFirstStart (first : Identifier) :
    ∀ fuel last tailRev input path next,
      ExportInternals.exportPathTail first fuel last tailRev input =
          .ok path next →
        path.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact inductionHypothesis component (component :: tailRev)
                  afterComponent path next result
      · unfold ExportInternals.finishExportPath at result
        cases result
        rfl

/-- An export path starts at the first identifier token that it retains. -/
theorem exportPath_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportPath (·.span) := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases identifier_ok_state_shape .exportDecl firstResult with
        ⟨token, found, tokenSpan, _tokens, _cursor⟩
      refine ⟨token, found, ?_⟩
      rw [tokenSpan]
      exact (exportPathTail_keepsFirstStart first
        (afterFirst.remainingCount + 1) first [] afterFirst path next
        result).symm

private theorem exportPathTail_cursorMonotoneOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
      Parser.CursorMonotoneOnSuccess
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact Nat.le_trans
                  (symbol_cursorMonotoneOnSuccess .dot .exportDecl
                    input dot afterDot dotResult)
                  (Nat.le_trans
                    (identifier_cursorMonotoneOnSuccess .exportDecl
                      afterDot component afterComponent componentResult)
                    (inductionHypothesis component (component :: tailRev)
                      afterComponent path next result))
      · unfold ExportInternals.finishExportPath at result
        cases result
        exact Nat.le_refl _

/-- Successful export-path parsing never rewinds the parser cursor. -/
theorem exportPath_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportPath := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact Nat.le_trans
        (identifier_cursorMonotoneOnSuccess .exportDecl
          input first afterFirst firstResult)
        (exportPathTail_cursorMonotoneOnSuccess first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result)

end Solcore.Syntax.Parser
