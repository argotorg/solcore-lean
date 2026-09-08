import Solcore.Test.SyntaxPostfixTailProgressSupport
import Solcore.Syntax.Parser.UnrestrictedFuelElementContract

/-! Index children need not advance: the closing bracket can finish the
suffix. Call lists instead reject stationary success as noProgress. A child
that preserves file/window but rewinds and replaces tokens gives a finite
independent index trace exceeding the production remaining-count fuel. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxPostfixTailProgressProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals SyntaxPostfixTailProgressSupport

private def indexBefore : Remainder := remainder #[sym 0 1 .leftBracket, sym 1 2 .rightBracket] 0 2
private def indexValue : Expr := postfixIndexTraceValue fixed fixed (span 0 1) (span 1 2)

private theorem index_opening : ExactTokenParses (.symbol .leftBracket) indexBefore
    (span 0 1) { indexBefore with cursor := 1 } :=
  ⟨⟨by decide, rfl⟩, rfl⟩
private theorem index_closing : ExactTokenParses (.symbol .rightBracket) { indexBefore with cursor := 1 }
    (span 1 2) { indexBefore with cursor := 2 } :=
  ⟨⟨by decide, rfl⟩, rfl⟩

theorem stationary_index_has_independent_trace :
    PostfixTailTraceParses (childTrace id) source 6 indexBefore fixed indexValue
      { indexBefore with cursor := 2 } [] := by
  apply PostfixTailTraceParses.index (indexEvents := []) (tailEvents := [])
    (span 0 1) (span 1 2) index_opening ⟨rfl, rfl, rfl⟩ index_closing
  exact .done (by simp [PostfixSuffixAbsentAt, TokenKindAbsentAt, TokenAt, indexBefore, remainder])

theorem stationary_index_child_does_not_advance (prior : List ParseDiagnostic) :
    child id { state indexBefore prior with cursor := 1 } =
      .ok fixed { state indexBefore prior with cursor := 1 } := rfl

/-- Whole Reply equality also retains arbitrary incoming diagnostic multiplicity. -/
theorem stationary_index_executes (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child id) block 2 fixed (state indexBefore prior) =
      .ok indexValue { state indexBefore prior with cursor := 2 } := rfl

/-- The grammar-to-execution theorem consumes the independent token derivation. -/
theorem stationary_index_trace_executes_eventually (block : Parser Block) (prior : List ParseDiagnostic) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      postfixTail (child id) block fuel fixed (state indexBefore prior) = .ok indexValue output ∧
      output.declarativeRemainder = { indexBefore with cursor := 2 } ∧
      output.diagnostics = (state indexBefore prior).diagnostics ++ [] :=
  postfixTail_trace_success_complete_eventually (child_success_complete id)
    (child_success_context id (fun _ => rfl)) block stationary_index_has_independent_trace

private def callBefore : Remainder :=
  remainder #[sym 0 1 .leftParen, sym 1 2 .plus, sym 2 3 .rightParen] 0 3

theorem stationary_call_reaches_noProgress (block : Parser Block) (prior : List ParseDiagnostic) (fuel : Nat) :
    postfixTail (child id) block (fuel + 1) fixed (state callBefore prior) =
      .invariant (.noProgress .expression (span 1 2)) := rfl

/-- Finite-trace completeness excludes a fictitious ordinary call success;
the exact same child does have the independent index trace above. -/
theorem stationary_call_has_no_independent_success (block : Parser Block) (prior : List ParseDiagnostic) :
    ¬ ∃ value after trace, PostfixTailTraceParses (childTrace id) source 6
      callBefore fixed value after trace := by
  rintro ⟨value, after, trace, parsed⟩
  rcases postfixTail_trace_success_complete_eventually (child_success_complete id)
      (child_success_context id (fun _ => rfl)) block (input := state callBefore prior) parsed with ⟨bound, executes⟩
  rcases executes (bound + 1) (Nat.le_succ _) with ⟨output, result, _⟩
  rw [stationary_call_reaches_noProgress] at result
  contradiction

private def initialTokens : Array Token := #[name 0 1, sym 1 2 .leftBracket]
private def firstTokens : Array Token := #[sym 2 3 .rightBracket, sym 3 4 .leftBracket]
private def finalTokens : Array Token := #[sym 4 5 .rightBracket, name 5 6]
private def rewind (input : Remainder) : Remainder := {
  input with tokens := if input.tokens = initialTokens then firstTokens else finalTokens, cursor := 0
}
private def rewindBefore : Remainder := remainder initialTokens 1 2
private def afterFirst : Remainder := remainder firstTokens 0 2
private def afterSecond : Remainder := remainder finalTokens 0 2
private def firstValue : Expr := postfixIndexTraceValue fixed fixed (span 1 2) (span 2 3)
private def finalValue : Expr := postfixIndexTraceValue firstValue fixed (span 3 4) (span 4 5)

private theorem first_opening : ExactTokenParses (.symbol .leftBracket) rewindBefore (span 1 2)
    { rewindBefore with cursor := 2 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem first_child : childTrace rewind source 6 { rewindBefore with cursor := 2 }
    fixed afterFirst [] := ⟨rfl, rfl, rfl⟩
private theorem first_closing : ExactTokenParses (.symbol .rightBracket) afterFirst (span 2 3)
    { afterFirst with cursor := 1 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem second_opening : ExactTokenParses (.symbol .leftBracket) { afterFirst with cursor := 1 }
    (span 3 4) { afterFirst with cursor := 2 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem second_child : childTrace rewind source 6 { afterFirst with cursor := 2 }
    fixed afterSecond [] := ⟨rfl, rfl, rfl⟩
private theorem second_closing : ExactTokenParses (.symbol .rightBracket) afterSecond (span 4 5)
    { afterSecond with cursor := 1 } := ⟨⟨by decide, rfl⟩, rfl⟩
private theorem final_stops : PostfixSuffixAbsentAt { afterSecond with cursor := 1 } := by
  have found : TokenAt finalTokens 2 1 (name 5 6) := ⟨by decide, rfl⟩
  exact ⟨absent_of_token found (by decide), absent_of_token found (by decide), absent_of_token found (by decide)⟩

/-- The independently defined child has all five trace contracts and ordinary
execution over every State; full-window context does not prohibit rewinding. -/
theorem rewinding_child_has_five_contracts_and_is_ordinary :
    ParserTraceSuccessSound (child rewind) (childTrace rewind) ∧
    ParserTraceSuccessComplete (child rewind) (childTrace rewind) ∧
    ParserSuccessContext (child rewind) ∧
    ParserTraceRejectSound (child rewind) neverReject ∧
    ParserTraceRejectComplete (child rewind) neverReject ∧
    Parser.Ordinary (child rewind) :=
  ⟨child_success_sound rewind, child_success_complete rewind, child_success_context rewind (fun _ => rfl),
    child_reject_sound rewind, child_reject_complete rewind, child_ordinary rewind⟩

theorem rewinding_has_finite_independent_trace :
    PostfixTailTraceParses (childTrace rewind) source 6 rewindBefore fixed finalValue
      { afterSecond with cursor := 1 } [] :=
  .index (span 1 2) (span 2 3) first_opening first_child first_closing
    (.index (span 3 4) (span 4 5) second_opening second_child second_closing (.done final_stops))

theorem rewinding_trace_executes_eventually (block : Parser Block) (prior : List ParseDiagnostic) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∃ output,
      postfixTail (child rewind) block fuel fixed (state rewindBefore prior) = .ok finalValue output ∧
      output.declarativeRemainder = { afterSecond with cursor := 1 } ∧
      output.diagnostics = (state rewindBefore prior).diagnostics ++ [] :=
  postfixTail_trace_success_complete_eventually (child_success_complete rewind)
    (child_success_context rewind (fun _ => rfl)) block rewinding_has_finite_independent_trace

/-- The initial remaining count is one. Two suffixes consume all two units,
leaving no fuel to observe the final non-suffix token. -/
theorem rewinding_production_fuel_is_insufficient (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child rewind) block ((state rewindBefore prior).remainingCount + 1)
      fixed (state rewindBefore prior) = .invariant (.fuelExhausted .expression (span 5 6)) := rfl

theorem rewinding_fuel_three_executes (block : Parser Block) (prior : List ParseDiagnostic) :
    postfixTail (child rewind) block 3 fixed (state rewindBefore prior) =
      .ok finalValue (state { afterSecond with cursor := 1 } prior) := rfl

theorem rewinding_has_no_strict_progress_contract (nestedFuel : Nat) :
    ¬ UnrestrictedFuelElementContract (child rewind) nestedFuel := by
  intro contract
  have result : child rewind { state rewindBefore [] with cursor := 2 } =
      .ok fixed (state afterFirst []) := rfl
  have progress := contract.cursorLtOnSuccess result
  change 2 < 0 at progress
  omega

end Solcore.Test.SyntaxPostfixTailProgressProperties
