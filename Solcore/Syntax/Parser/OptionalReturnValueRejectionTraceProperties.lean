import Solcore.Syntax.DeclarativeReturnStatementRejectionTraceGrammar
import Solcore.Syntax.Parser.ExpressionDiagnosticTraceContracts
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Statement.Simple

/-! Rejected optional return values preserve semicolon-first priority and the
inner expression's exact failure report and complete preceding event sequence. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.StatementSimpleInternals

variable {expression : Parser Expr}
  {expressionRejects : SourceId → Nat → DeclarativeGrammar.Remainder →
    DeclarativeGrammar.Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem semicolon_absent {input : State}
    (absent : DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.symbol .semicolon)) : isSymbol input .semicolon = false := by
  apply Bool.eq_false_iff.mpr
  intro present
  rcases symbol_eq_ok_of_isSymbol_eq_true .semicolon .statement present with ⟨token, result⟩
  exact absent ⟨token.span, (symbol_ok_tokenAt .semicolon .statement result).1⟩

theorem optionalReturnValue_reject_trace_sound
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    {input rejected : State} {failure : Failure}
    (result : optionalReturnValue expression input = .reject failure rejected) :
    ∃ trace, DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder rejected.declarativeRemainder
      failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  unfold optionalReturnValue getState at result
  simp only [bind] at result
  cases present : isSymbol input .semicolon with
  | true => simp [present, pure] at result
  | false =>
      simp only [present, Bool.false_eq_true, if_false] at result
      cases expressionResult : expression input with
      | invariant error => simp [expressionResult] at result
      | ok value next => simp [expressionResult, pure] at result
      | reject expressionFailure expressionRejected =>
          simp only [expressionResult] at result
          cases result
          rcases rejectSound expressionResult with ⟨trace, rejectedTrace, diagnostics⟩
          exact ⟨trace, .expressionRejected
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon present) rejectedTrace, diagnostics⟩

theorem optionalReturnValue_trace_reject_complete
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace) :
    ∃ failure rejected, optionalReturnValue expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  cases rejection with
  | expressionRejected absent rejectedTrace =>
      rcases rejectComplete rejectedTrace with ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
      exact ⟨failure, rejected, by
        simp only [optionalReturnValue, getState, bind, semicolon_absent absent,
          Bool.false_eq_true, if_false, result], afterEq, reportEq, diagnostics⟩

theorem optionalReturnValue_trace_reject_iff
    (rejectSound : ExpressionTraceRejectSound expression expressionRejects)
    (rejectComplete : ExpressionTraceRejectComplete expression expressionRejects)
    {input : State} {remainder : DeclarativeGrammar.Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic} :
    DeclarativeGrammar.OptionalReturnValueTraceRejects expressionRejects
      input.file.id input.window.endByte input.declarativeRemainder remainder diagnostic trace ↔
    ∃ failure rejected, optionalReturnValue expression input = .reject failure rejected ∧
      rejected.declarativeRemainder = remainder ∧ failure.toDiagnostic = diagnostic ∧
      rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact optionalReturnValue_trace_reject_complete rejectComplete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, diagnostics⟩
    rcases optionalReturnValue_reject_trace_sound rejectSound result with
      ⟨actualTrace, rejection, actualEq⟩
    have events : actualTrace = trace := List.append_cancel_left (actualEq.symm.trans diagnostics)
    simpa only [afterEq, reportEq, events] using rejection

end Solcore.Syntax.Parser.StatementSimpleInternals
