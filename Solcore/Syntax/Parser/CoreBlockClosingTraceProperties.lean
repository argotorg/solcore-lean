import Solcore.Syntax.DeclarativeCoreBlockTailTraceProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.Parser.Block
import Solcore.Syntax.Parser.ExactTokenPrimitiveRejectionTraceProperties

/-! Exact brace closing, tail-validation events, and silent closing rejection. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Independently supplied tail checks determine every diagnostic added by closing. -/
theorem closeCoreBlock_success_diagnostics_eq_of_trace
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input output : State} {body : Block} {trace : List ParseDiagnostic}
    (result : closeCoreBlock opening policy bodyRev input = .ok body output)
    (checked : DeclarativeGrammar.CoreBlockTailsDiagnosticTrace
      policy.declarative bodyRev.reverse trace) :
    output.diagnostics = input.diagnostics ++ trace := by
  rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
    ⟨actualTrace, actual, diagnostics⟩
  simpa only [actual.output_unique checked] using diagnostics

/-- The exact independent brace, source-order AST, remainder, and tail events
are equivalent to execution. The brace span stays existential because covering
it with the opening span need not retain enough information to recover it. -/
theorem closeCoreBlock_trace_success_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {body : Block} {remainder : DeclarativeGrammar.Remainder}
    {trace : List ParseDiagnostic} :
    ((∃ closingSpan,
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan remainder ∧
      body = { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse }) ∧
      DeclarativeGrammar.CoreBlockTailsDiagnosticTrace policy.declarative bodyRev.reverse trace) ↔
    ∃ output, closeCoreBlock opening policy bodyRev input = .ok body output ∧
      output.declarativeRemainder = remainder ∧
      output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · rintro ⟨⟨closingSpan, closingParsed, rfl⟩, checked⟩
    have closingResult := symbol_eq_ok_of_exactTokenParses .rightBrace .statement closingParsed
    have succeeds : ∃ output, closeCoreBlock opening policy bodyRev input = .ok
        { span := SourceSpan.cover opening.span closingSpan, value := bodyRev.reverse } output := by
      simp only [closeCoreBlock, bind, closingResult, modifyState, pure]
      exact ⟨_, rfl⟩
    rcases succeeds with ⟨output, result⟩
    rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
      ⟨actualSpan, _, actualClosing⟩
    exact ⟨output, result, actualClosing.output_unique closingParsed,
      closeCoreBlock_success_diagnostics_eq_of_trace opening policy bodyRev result checked⟩
  · rintro ⟨output, result, after, diagnostics⟩
    rcases closeCoreBlock_success_ordinary_sound opening policy bodyRev result with
      ⟨closingSpan, bodyEq, closingParsed⟩
    rcases closeCoreBlock_success_trace_sound opening policy bodyRev result with
      ⟨actualTrace, checked, actualDiagnostics⟩
    have events : actualTrace = trace :=
      List.append_cancel_left (actualDiagnostics.symm.trans diagnostics)
    exact ⟨⟨closingSpan, after ▸ closingParsed, bodyEq⟩, events ▸ checked⟩

/-- A missing closing brace rejects before tail validation can run. -/
theorem closeCoreBlock_reject_iff_symbol
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input rejected : State} {failure : Failure} :
    closeCoreBlock opening policy bodyRev input = .reject failure rejected ↔
      symbol .rightBrace .statement input = .reject failure rejected := by
  cases closingResult : symbol .rightBrace .statement input <;>
    simp only [closeCoreBlock, bind, closingResult, modifyState, pure,
      reduceCtorEq, Reply.reject.injEq, iff_self]

/-- Closing rejection retains the whole input and every prior event, and its
complete uncommitted report is exactly that of the required right brace. -/
theorem closeCoreBlock_reject_reports
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input rejected : State} {failure : Failure}
    (result : closeCoreBlock opening policy bodyRev input = .reject failure rejected) :
    rejected = input ∧
      DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder failure.toDiagnostic ∧
      rejected.diagnostics = input.diagnostics := by
  have primitive := (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mp result
  have stateEq := acceptToken_reject_state_shape (.symbol .rightBrace) .statement
    (· == .symbol .rightBrace) primitive
  subst rejected
  have reported := (symbol_reject_reports_iff .rightBrace .statement).mpr ⟨failure, primitive, rfl⟩
  exact ⟨rfl, reported.1, reported.2, rfl⟩

/-- Independent brace absence and its diagnostic report characterize exact
silent rejection, with no validity or prior-diagnostic assumptions. -/
theorem closeCoreBlock_reject_reports_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {diagnostic : ParseDiagnostic} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder diagnostic) ↔
      ∃ failure, closeCoreBlock opening policy bodyRev input = .reject failure input ∧
        failure.toDiagnostic = diagnostic := by
  rw [symbol_reject_reports_iff .rightBrace .statement]
  constructor
  · rintro ⟨failure, result, report⟩
    exact ⟨failure, (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mpr result, report⟩
  · rintro ⟨failure, result, report⟩
    exact ⟨failure, (closeCoreBlock_reject_iff_symbol opening policy bodyRev).mp result, report⟩

/-- The independent report also fixes all fields of the uncommitted failure. -/
theorem closeCoreBlock_reject_failure_iff
    (opening : Token) (policy : TailExpressionPolicy) (bodyRev : List Statement)
    {input : State} {failure : Failure} :
    (DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
        (.symbol .rightBrace) ∧
      DeclarativeGrammar.RejectAtReports input.file.id input.window.endByte
        { head := .symbol .rightBrace, tail := [] } .statement
        input.declarativeRemainder failure.toDiagnostic) ↔
      closeCoreBlock opening policy bodyRev input = .reject failure input := by
  constructor
  · intro reported
    rcases (closeCoreBlock_reject_reports_iff opening policy bodyRev).mp reported with
      ⟨actual, result, report⟩
    exact Failure.toDiagnostic_injective report ▸ result
  · intro result
    exact (closeCoreBlock_reject_reports_iff opening policy bodyRev).mpr ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser
