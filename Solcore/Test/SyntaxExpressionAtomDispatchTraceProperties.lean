import Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties

/-! Concrete ordered atom selections, independent of recursive expression or
block outcomes. Only the currently visible token participates in these guards. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomDispatchTraceInternals
open Solcore.Syntax.Parser.ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "expression-atom-selection.sol" }
private def span : SourceSpan := { source, startByte := 2, endByte := 9 }
private def token (value : TokenKind) : Token := { span, value }
private def remainder (kinds : List TokenKind) (endIndex cursor : Nat) : Remainder :=
  { tokens := (kinds.map token).toArray, endIndex, cursor }
private def state (kinds : List TokenKind) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (kinds.map token).toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def sampleKind : ExpressionAtomDispatchBranch → TokenKind
  | .literal => .decimalLiteral "7"
  | .name => .identifier "a-b"
  | .dotConstructor => .symbol .dot
  | .proxy => .symbol .at
  | .parenthesized => .symbol .leftParen
  | .array => .symbol .leftBracket
  | .lambda => .keyword .lamKw
  | .final => .symbol .plus

/-- Every branch is witnessed directly by token premises, not parser evaluation. -/
theorem all_eight_independent_selections (branch : ExpressionAtomDispatchBranch) :
    ExpressionAtomDispatchSelects (remainder [sampleKind branch] 1 0) branch := by
  cases branch <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
      remainder, sampleKind, token]

theorem boolean_keywords_and_written_identifiers_are_names :
    ExpressionAtomDispatchSelects (remainder [.keyword .trueKw] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .falseKw] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "true"] 1 0) .name ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "false"] 1 0) .name ∧
    token (.keyword .trueKw) ≠ token (.identifier "true") ∧
    token (.keyword .falseKw) ≠ token (.identifier "false") := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide⟩ <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenAt, remainder, token]

theorem hexadecimal_and_string_select_literals :
    ExpressionAtomDispatchSelects (remainder [.hexadecimalLiteral "0xff"] 1 0) .literal ∧
    ExpressionAtomDispatchSelects (remainder [.stringLiteral "true"] 1 0) .literal := by
  constructor <;> constructor <;> simp [CoreLiteralStartsAt, TokenAt, remainder, token]

theorem lambda_keyword_and_written_identifier_are_distinct :
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 1 0) .lambda ∧
    ExpressionAtomDispatchSelects (remainder [.identifier "lam"] 1 0) .name := by
  refine ⟨all_eight_independent_selections .lambda, ?_⟩
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenAt, remainder, token]

/-- Backing presence is insufficient outside the numeric window. Numeric
membership is also insufficient when no backing token exists. -/
theorem invisible_tokens_select_final :
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 0 0) .final ∧
    ExpressionAtomDispatchSelects (remainder [] 7 0) .final ∧
    ExpressionAtomDispatchSelects (remainder [.decimalLiteral "7"] 1 4) .final ∧
    (remainder [.keyword .lamKw] 0 0).tokens[0]? = some (token (.keyword .lamKw)) ∧
    (remainder [] 7 0).cursor < (remainder [] 7 0).endIndex ∧
    (remainder [.decimalLiteral "7"] 1 4).endIndex <
      (remainder [.decimalLiteral "7"] 1 4).cursor := by
  refine ⟨?_, ?_, ?_, rfl, by decide, by decide⟩ <;> constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, remainder]

theorem same_carrier_window_changes_selection :
    (remainder [.keyword .lamKw] 1 0).tokens = (remainder [.keyword .lamKw] 0 0).tokens ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 1 0) .lambda ∧
    ExpressionAtomDispatchSelects (remainder [.keyword .lamKw] 0 0) .final :=
  ⟨rfl, all_eight_independent_selections .lambda, invisible_tokens_select_final.1⟩

/-- Equal observations transport the chosen branch even with different
carriers, numeric positions, and unobserved suffixes. -/
theorem shifted_current_token_keeps_selection (branch : ExpressionAtomDispatchBranch) :
    ExpressionAtomDispatchSelects
      (remainder [.symbol .plus, sampleKind branch, .keyword .lamKw] 2 1) branch := by
  apply (ExpressionAtomDispatchSelects.congr_of_tokenAt
    (left := remainder [sampleKind branch] 1 0) (right := remainder
      [.symbol .plus, sampleKind branch, .keyword .lamKw] 2 1) (branch := branch) ?_).mp
      (all_eight_independent_selections branch)
  intro current
  simp [TokenAt, remainder]

/-- Every direct witness determines the real guard and its complete raw Reply,
without a success, rejection, frame, or ordinary contract for either child. -/
theorem all_eight_raw_replies (nested : Parser Expr) (block : Parser Block)
    (branch : ExpressionAtomDispatchBranch) (prior : List ParseDiagnostic) :
    selectedBranch (state [sampleKind branch] 1 0 prior) = branch ∧
    expressionAtomCore nested block (state [sampleKind branch] 1 0 prior) =
      rawParser nested block branch (state [sampleKind branch] 1 0 prior) :=
  ⟨selectedBranch_eq_iff.mpr (all_eight_independent_selections branch),
    expressionAtomCore_eq_raw_of_selection nested block (all_eight_independent_selections branch)⟩

theorem boolean_names_run_identifier_expression (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.keyword .trueKw] 1 0 prior) =
      identifierExpression (state [.keyword .trueKw] 1 0 prior) ∧
    expressionAtomCore nested block (state [.keyword .falseKw] 1 0 prior) =
      identifierExpression (state [.keyword .falseKw] 1 0 prior) ∧
    expressionAtomCore nested block (state [.identifier "true"] 1 0 prior) =
      identifierExpression (state [.identifier "true"] 1 0 prior) ∧
    expressionAtomCore nested block (state [.identifier "false"] 1 0 prior) =
      identifierExpression (state [.identifier "false"] 1 0 prior) :=
  ⟨expressionAtomCore_eq_raw_of_selection nested block (input := state [.keyword .trueKw] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.keyword .falseKw] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.identifier "true"] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.2.1,
    expressionAtomCore_eq_raw_of_selection nested block (input := state [.identifier "false"] 1 0 prior)
      boolean_keywords_and_written_identifiers_are_names.2.2.2.1⟩

/-- A non-lambda atom never invokes the supplied block parser. -/
theorem unselected_block_cannot_change_reply (nested : Parser Expr) (left right : Parser Block)
    {input : State} {branch : ExpressionAtomDispatchBranch}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder branch)
    (notLambda : branch ≠ .lambda) :
    expressionAtomCore nested left input = expressionAtomCore nested right input := by
  rw [expressionAtomCore_eq_raw_of_selection nested left selected,
    expressionAtomCore_eq_raw_of_selection nested right selected]
  cases branch <;> first | rfl | exact False.elim (notLambda rfl)

/-- A selected lambda invokes the supplied block, but not the atom's separate
recursive expression argument. The statement preserves even invariant Replies. -/
theorem lambda_selection_ignores_nested (left right : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore left block (state [.keyword .lamKw] 1 0 prior) =
      expressionAtomCore right block (state [.keyword .lamKw] 1 0 prior) := by
  rw [expressionAtomCore_eq_raw_of_selection left block (input := state [.keyword .lamKw] 1 0 prior)
      (all_eight_independent_selections .lambda),
    expressionAtomCore_eq_raw_of_selection right block (input := state [.keyword .lamKw] 1 0 prior)
      (all_eight_independent_selections .lambda)]
  rfl

theorem leaf_selection_ignores_both_children (nestedLeft nestedRight : Parser Expr)
    (blockLeft blockRight : Parser Block) {input : State} {branch : ExpressionAtomDispatchBranch}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder branch)
    (leaf : branch ∈ [.literal, .name, .proxy, .final]) :
    expressionAtomCore nestedLeft blockLeft input = expressionAtomCore nestedRight blockRight input := by
  rw [expressionAtomCore_eq_raw_of_selection nestedLeft blockLeft selected,
    expressionAtomCore_eq_raw_of_selection nestedRight blockRight selected]
  cases branch <;> first | rfl | simp at leaf

theorem final_selection_keeps_full_state (nested : Parser Expr) (block : Parser Block) {input : State}
    (selected : ExpressionAtomDispatchSelects input.declarativeRemainder .final) :
    expressionAtomCore nested block input = .reject {
      span := input.currentSpan, found := input.peekKind?
      expected := { head := .expression, tail := [] }, context := .expression
    } input := by
  rw [expressionAtomCore_eq_raw_of_selection nested block selected]
  rfl

private def eofFailure : Failure := {
  span := { source, startByte := 99, endByte := 99 }, found := none
  expected := { head := .expression, tail := [] }, context := .expression
}

theorem invisible_tokens_preserve_final_reply (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.keyword .lamKw] 0 0 prior) =
      .reject eofFailure (state [.keyword .lamKw] 0 0 prior) ∧
    expressionAtomCore nested block (state [] 7 0 prior) = .reject eofFailure (state [] 7 0 prior) ∧
    expressionAtomCore nested block (state [.decimalLiteral "7"] 1 4 prior) =
      .reject eofFailure (state [.decimalLiteral "7"] 1 4 prior) :=
  ⟨final_selection_keeps_full_state nested block invisible_tokens_select_final.1,
    final_selection_keeps_full_state nested block invisible_tokens_select_final.2.1,
    final_selection_keeps_full_state nested block invisible_tokens_select_final.2.2.1⟩

theorem unexpected_token_report_is_not_committed (nested : Parser Expr) (block : Parser Block)
    (prior : List ParseDiagnostic) :
    expressionAtomCore nested block (state [.symbol .plus] 1 0 prior) = .reject {
      span, found := some (.symbol .plus)
      expected := { head := .expression, tail := [] }, context := .expression
    } (state [.symbol .plus] 1 0 prior) ∧
    (state [.symbol .plus] 1 0 prior).diagnostics = prior := by
  refine ⟨final_selection_keeps_full_state nested block (all_eight_independent_selections .final), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

theorem prior_diagnostics_do_not_select_branches (kinds : List TokenKind) (endIndex cursor : Nat)
    (left right : List ParseDiagnostic) :
    selectedBranch (state kinds endIndex cursor left) = selectedBranch (state kinds endIndex cursor right) :=
  selectedBranch_eq_of_remainder_eq rfl

end Solcore.Test.SyntaxExpressionAtomDispatchTraceProperties
