import Solcore.Syntax.Parser.Term

/-! Contracts for the canonical statement dispatch boundary. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- Recognized-statement fallback preserves either branch's provenance. -/
theorem recognizedStatementOrFallback_validFor
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryValid : primary.ValidFor valueValid)
    (fallbackValid : fallback.ValidFor valueValid) :
    (recognizedStatementOrFallback primary fallback).ValidFor valueValid := by
  intro input inputValid
  have primaryContract := primaryValid input inputValid
  unfold recognizedStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      rw [primaryResult] at primaryContract
      have fallbackContract := fallbackValid input inputValid
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.ValidFor]
          exact ⟨primaryContract.1, inputValid, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          let reset : State := {
            next with diagnosticsRev := input.diagnosticsRev
          }
          have resetValid : reset.ValidFor := {
            tokens := fallbackContract.2.1.tokens
            cursor_le_endIndex := fallbackContract.2.1.cursor_le_endIndex
            endIndex_le_size := fallbackContract.2.1.endIndex_le_size
            endByte_le_source := fallbackContract.2.1.endByte_le_source
            endByte_boundary := fallbackContract.2.1.endByte_boundary
            diagnosticsRev := by
              intro diagnostic member
              simpa [reset, fallbackContract.2.2] using
                inputValid.diagnosticsRev diagnostic member
          }
          have emittedValid := resetValid.emit_validFor failure.toDiagnostic
            (by simpa [reset, fallbackContract.2.2] using
              failure.toDiagnostic_span_validFor primaryContract.1)
          simp only [Reply.ValidFor]
          exact ⟨fallbackContract.1, emittedValid,
            by simpa [reset, State.emit] using fallbackContract.2.2⟩

/-- Recognized-statement fallback preserves every ordinary token window. -/
theorem recognizedStatementOrFallback_preservesTokenWindow
    (primary fallback : Parser Statement)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokenWindow
      (recognizedStatementOrFallback primary fallback) := by
  intro input
  have primaryContract := primaryShape input
  unfold recognizedStatementOrFallback
  cases primaryResult : primary input with
  | invariant error => trivial
  | ok value next =>
      rw [primaryResult] at primaryContract
      simpa only [primaryResult] using primaryContract
  | reject failure failedState =>
      have fallbackContract := fallbackShape input
      cases fallbackResult : fallback input with
      | invariant error => trivial
      | reject fallbackFailure fallbackState =>
          simp only [Reply.PreservesTokenWindow]
          exact ⟨trivial, trivial⟩
      | ok value next =>
          rw [fallbackResult] at fallbackContract
          simpa only [primaryResult, fallbackResult, State.emit,
            Reply.PreservesTokenWindow] using fallbackContract

/-- Successful fallback retains the selected branch's token carrier. -/
theorem recognizedStatementOrFallback_preservesTokensOnSuccess
    (primary fallback : Parser Statement)
    (primaryShape : Parser.PreservesTokenWindow primary)
    (fallbackShape : Parser.PreservesTokenWindow fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedStatementOrFallback primary fallback) :=
  (recognizedStatementOrFallback_preservesTokenWindow primary fallback
    primaryShape fallbackShape).preservesTokensOnSuccess

/-- Success-only carrier contracts also compose through this boundary. -/
theorem recognizedStatementOrFallback_preservesTokensOnSuccess_of_success
    (primary fallback : Parser Statement)
    (primaryPreserves : Parser.PreservesTokensOnSuccess primary)
    (fallbackPreserves : Parser.PreservesTokensOnSuccess fallback) :
    Parser.PreservesTokensOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have preserved := primaryPreserves input primaryValue afterPrimary
        primaryResult
      cases result
      exact preserved
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have preserved := fallbackPreserves input fallbackValue afterFallback
            fallbackResult
          cases result
          exact preserved

/-- Recognized fallback never rewinds either successful branch. -/
theorem recognizedStatementOrFallback_cursorMonotoneOnSuccess
    (primary fallback : Parser Statement)
    (primaryMonotone : Parser.CursorMonotoneOnSuccess primary)
    (fallbackMonotone : Parser.CursorMonotoneOnSuccess fallback) :
    Parser.CursorMonotoneOnSuccess
      (recognizedStatementOrFallback primary fallback) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have monotone := primaryMonotone input primaryValue afterPrimary
        primaryResult
      cases result
      exact monotone
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have monotone := fallbackMonotone input fallbackValue afterFallback
            fallbackResult
          cases result
          exact monotone

/-- Success begins at the input token of whichever branch was selected. -/
theorem recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess
    (primary fallback : Parser Statement)
    (primaryStarts : Parser.StartsAtCurrentTokenOnSuccess primary (·.span))
    (fallbackStarts : Parser.StartsAtCurrentTokenOnSuccess fallback (·.span)) :
    Parser.StartsAtCurrentTokenOnSuccess
      (recognizedStatementOrFallback primary fallback) (·.span) := by
  intro input value next result
  unfold recognizedStatementOrFallback at result
  cases primaryResult : primary input with
  | invariant error => simp [primaryResult] at result
  | ok primaryValue afterPrimary =>
      simp only [primaryResult] at result
      have starts := primaryStarts input primaryValue afterPrimary primaryResult
      cases result
      exact starts
  | reject failure failedState =>
      simp only [primaryResult] at result
      cases fallbackResult : fallback input with
      | invariant error => simp [fallbackResult] at result
      | reject fallbackFailure fallbackState => simp [fallbackResult] at result
      | ok fallbackValue afterFallback =>
          simp only [fallbackResult] at result
          have starts := fallbackStarts input fallbackValue afterFallback
            fallbackResult
          cases result
          exact starts

/-- The compositional boundary needed by the complete statement dispatch. -/
structure StatementParserContract (valueValid : SourceFile → Statement → Prop)
    (parser : Parser Statement) : Prop where
  validFor : parser.ValidFor valueValid
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

namespace StatementParserContract

theorem preservesTokensOnSuccess
    {valueValid : SourceFile → Statement → Prop} {parser : Parser Statement}
    (contract : StatementParserContract valueValid parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

end StatementParserContract

/-- Both branch contracts compose through recognized fallback. -/
theorem recognizedStatementOrFallback_contract
    {valueValid : SourceFile → Statement → Prop}
    (primary fallback : Parser Statement)
    (primaryContract : StatementParserContract valueValid primary)
    (fallbackContract : StatementParserContract valueValid fallback) :
    StatementParserContract valueValid
      (recognizedStatementOrFallback primary fallback) := {
  validFor := recognizedStatementOrFallback_validFor primary fallback
    primaryContract.validFor fallbackContract.validFor
  preservesTokenWindow :=
    recognizedStatementOrFallback_preservesTokenWindow primary fallback
      primaryContract.preservesTokenWindow fallbackContract.preservesTokenWindow
  cursorMonotoneOnSuccess :=
    recognizedStatementOrFallback_cursorMonotoneOnSuccess primary fallback
      primaryContract.cursorMonotoneOnSuccess
      fallbackContract.cursorMonotoneOnSuccess
  startsAtCurrentTokenOnSuccess :=
    recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess primary fallback
      primaryContract.startsAtCurrentTokenOnSuccess
      fallbackContract.startsAtCurrentTokenOnSuccess
}

end Solcore.Syntax.Parser.TermInternals
