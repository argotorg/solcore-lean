import Solcore.Syntax.Parser.LambdaExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceStateProperties
import Solcore.Syntax.DeclarativeLambdaExpressionTraceProperties
import Solcore.Syntax.Parser.TypeUnrestrictedFuelTotalityProperties

/-! Raw lambda outcome existence follows from ordinary execution of the
supplied block and the concrete parameter/type parsers. It is not inferred
from independent uniqueness or disjointness. Body context, carrier, progress,
and completeness laws are unnecessary for these existence results. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {block : Parser Block}
  {blockTrace : SourceId → Nat → Remainder → Block → Remainder → List ParseDiagnostic → Prop}
  {blockRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

private theorem ordinary_bind {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstOrdinary : Parser.Ordinary first) (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with ⟨value, after, result⟩ | ⟨failure, rejected, result⟩
  · rcases nextOrdinary value after with ⟨value, output, nextResult⟩ | ⟨failure, rejected, nextResult⟩
    · exact .inl ⟨value, output, by simp only [bind, result, nextResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [bind, result, nextResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [bind, result]⟩

/-- Optional return parsing has an ordinary result on every State, even when
the active window or backing tokens are noncanonical. -/
theorem optionalLambdaReturnType_ordinary_unrestricted : Parser.Ordinary optionalLambdaReturnType := by
  intro input
  by_cases present : isSymbol input .arrow = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with ⟨arrow, arrowResult⟩
    have equation := optionalLambdaReturnType_eq_of_present (symbol_ok_tokenAt .arrow .typeExpr arrowResult).1
    rcases typeExpr_ordinary { input with cursor := input.cursor + 1 } with
      ⟨type, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨some type, output, by rw [equation, result]⟩
    · exact .inr ⟨failure, rejected, by rw [equation, result]⟩
  · exact .inl ⟨none, input, optionalLambdaReturnType_eq_none_of_absent
      (symbolAbsentAt_of_isSymbol_eq_false .arrow (Bool.eq_false_iff.mpr present))⟩

theorem optionalLambdaReturnType_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    optionalLambdaReturnType input ≠ .invariant error :=
  optionalLambdaReturnType_ordinary_unrestricted.ne_invariant input error

/-- Every ordinary block parser produces an ordinary raw lambda parser. The
body need not preserve the input source, window, or token carrier for this law. -/
theorem lambdaExpression_ordinary_unrestricted (blockOrdinary : Parser.Ordinary block) :
    Parser.Ordinary (lambdaExpression block) := by
  unfold lambdaExpression
  apply ordinary_bind (keyword_ordinary .lamKw .expression)
  intro marker
  apply ordinary_bind lambdaParameters_ordinary_unrestricted
  intro parameters
  apply ordinary_bind optionalLambdaReturnType_ordinary_unrestricted
  intro returnType
  apply ordinary_bind blockOrdinary
  intro body input
  exact .inl ⟨_, input, rfl⟩

theorem lambdaExpression_ne_invariant_unrestricted
    (blockOrdinary : Parser.Ordinary block) (input : State) (error : ParserInvariantError) :
    lambdaExpression block input ≠ .invariant error :=
  (lambdaExpression_ordinary_unrestricted blockOrdinary).ne_invariant input error

/-- Concrete ordinary execution supplies the witness; the two body soundness
contracts supply its exact raw trace. No body completeness or frame is used. -/
theorem lambdaExpression_exists_trace_outcome
    (successSound : ParserTraceSuccessSound block blockTrace)
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (blockOrdinary : Parser.Ordinary block) (input : State) :
    (∃ value output trace,
      lambdaExpression block input = .ok value output ∧
      LambdaExpressionTraceParses blockTrace input.file.id input.window.endByte
        input.declarativeRemainder value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      lambdaExpression block input = .reject failure rejected ∧
      LambdaExpressionTraceRejects blockRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaExpression_ordinary_unrestricted blockOrdinary input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaExpression_trace_success_sound successSound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaExpression_reject_trace_sound rejectSound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

/-- The same execution argument witnesses an outcome for every independent
source/endByte/remainder, without imposing a valid token window or source file. -/
theorem lambdaExpressionTrace_outcome_exists
    (successSound : ParserTraceSuccessSound block blockTrace)
    (rejectSound : ParserTraceRejectSound block blockRejects)
    (blockOrdinary : Parser.Ordinary block) (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaExpressionTraceParses blockTrace source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaExpressionTraceRejects blockRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaExpression_exists_trace_outcome successSound rejectSound blockOrdinary state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
