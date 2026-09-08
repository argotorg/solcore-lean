import Solcore.Syntax.Parser.ExpressionAtomUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.LiteralExpressionTraceProperties
import Solcore.Syntax.Parser.ParenthesizedTraceCorrespondenceProperties
import Solcore.Syntax.Parser.DiagnosticTraceStateProperties

/-! The real literal leaf supplies the minimal progress contract at every
fuel. One atom layer then has ordinary outcomes on arbitrary numerical States;
this is not recursive expression or block trace closure. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTotalityProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

theorem literal_child_contract (fuel : Nat) :
    UnrestrictedFuelElementContract literalExpression fuel where
  endIndexOnSuccess result := by rw [literalExpression_success_state_shape result]
  cursorLtOnSuccess result := by
    rw [literalExpression_success_state_shape result]
    exact Nat.lt_succ_self _
  ordinary input _ := by
    rcases coreLiteral_ordinary input with ⟨literal, next, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨{ span := literal.span, value := .literal literal }, next,
        by simp only [literalExpression, bind, result, pure]⟩
    · exact .inr ⟨failure, rejected, by simp only [literalExpression, bind, result]⟩

private def source : SourceId := { origin := .main, path := "atom-unrestricted.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def fixedBlock : Block := { span := span 0 0, value := [] }
private def emptyBlock : Parser Block := pure fixedBlock
private theorem emptyBlock_ordinary : Parser.Ordinary emptyBlock := fun input => .inl ⟨fixedBlock, input, rfl⟩

private def OrdinaryAt {α : Type} (parser : Parser α) (input : State) : Prop :=
  (∃ value next, parser input = .ok value next) ∨
    (∃ failure next, parser input = .reject failure next)

/-- The child has no validity premise; the two loop bounds are still explicit. -/
theorem literal_tuple_tail_ordinary (nestedFuel loopFuel : Nat) (opening : Token)
    (elementsRev : List Expr) (input : State)
    (loopAdequate : input.remainingCount < loopFuel)
    (nestedAdequate : input.remainingCount < nestedFuel + 1) :
    OrdinaryAt (tupleTail literalExpression opening loopFuel elementsRev) input :=
  tupleTail_ordinary_of_unrestrictedElementFuel literalExpression nestedFuel
    (literal_child_contract nestedFuel) opening loopFuel elementsRev input loopAdequate nestedAdequate

/-- Raw grouping/tuples, arrays, and dot constructors share only the explicit
remaining-count bound. No source, token-span, diagnostic, or ValidFor premise is hidden. -/
theorem literal_raw_branches_ordinary (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    OrdinaryAt (parenthesized literalExpression) input ∧
    OrdinaryAt (arrayLiteral literalExpression) input ∧
    OrdinaryAt (dotConstructor literalExpression) input :=
  ⟨parenthesized_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate,
    arrayLiteral_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate,
    dotConstructor_ordinary_of_unrestrictedElementFuel literalExpression fuel
      (literal_child_contract fuel) input adequate⟩

/-- An explicitly supplied ordinary block discharges the final child premise.
This parser contains just one dispatch layer over literal children. -/
theorem literal_core_and_public_ordinary (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel + 1) :
    OrdinaryAt (expressionAtomCore literalExpression emptyBlock) input ∧
    OrdinaryAt (expressionAtom literalExpression emptyBlock) input :=
  ⟨expressionAtomCore_ordinary_of_unrestrictedElementFuel literalExpression emptyBlock fuel
      (literal_child_contract fuel) emptyBlock_ordinary input adequate,
    expressionAtom_ordinary_of_unrestrictedElementFuel literalExpression emptyBlock fuel
      (literal_child_contract fuel) emptyBlock_ordinary input adequate⟩

private def numeral : Token := { span := span 2 4, value := .decimalLiteral "42" }
private def fixture (tokens : Array Token) (cursor endIndex : Nat)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def overshot (prior : List ParseDiagnostic) : State := fixture #[numeral] 9 7 prior
private def hidden (prior : List ParseDiagnostic) : State := fixture #[numeral] 0 0 prior
private def missing (prior : List ParseDiagnostic) : State := fixture #[] 0 3 prior
private def eofFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .expression, tail := [] }, context := .expression
}

theorem malformed_carriers_are_not_valid (prior : List ParseDiagnostic) :
    ¬ (overshot prior).ValidFor ∧ ¬ (hidden prior).ValidFor ∧ ¬ (missing prior).ValidFor := by
  refine ⟨?_, ?_, ?_⟩
  · intro valid
    have bound := valid.cursor_le_endIndex
    change 9 ≤ 7 at bound
    omega
  · intro valid
    have bound := valid.endByte_le_source
    change 99 ≤ 0 at bound
    omega
  · intro valid
    have bound := valid.endIndex_le_size
    change 3 ≤ 0 at bound
    omega

/-- A stored but hidden literal cannot be mistaken for a present token, and
a missing backing token is distinct from a numerical end-of-window. -/
theorem malformed_lookahead (prior : List ParseDiagnostic) :
    (hidden prior).tokens[0]? = some numeral ∧ (hidden prior).peek? = none ∧
    (hidden prior).atEnd = true ∧ (missing prior).peek? = none ∧
    (missing prior).atEnd = false ∧ (overshot prior).remainingCount = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem malformed_core_and_public_outcomes (prior : List ParseDiagnostic) :
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (overshot prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (overshot prior)) ∧
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (hidden prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (hidden prior)) ∧
    (OrdinaryAt (expressionAtomCore literalExpression emptyBlock) (missing prior) ∧
      OrdinaryAt (expressionAtom literalExpression emptyBlock) (missing prior)) :=
  ⟨literal_core_and_public_ordinary 0 (overshot prior) (by change 0 < 1; decide),
    literal_core_and_public_ordinary 0 (hidden prior) (by change 0 < 1; decide),
    literal_core_and_public_ordinary 3 (missing prior) (by change 3 < 4; decide)⟩

private theorem absent_core (input : State) (noToken : input.peek? = none) :
    expressionAtomCore literalExpression emptyBlock input =
      rejectAt input { head := .expression, tail := [] } .expression := by
  simp only [expressionAtomCore, isCoreLiteral, isBooleanValue, isIdentifier, isSymbol,
    isKeyword, State.peekKind?, noToken, Option.map_none]
  rfl

/-- Overshot and hidden-token ends retain the whole State and arbitrary prior
events. The uncommitted expression failure is at endByte, not the stored literal. -/
theorem numerical_end_rejects_without_events (prior : List ParseDiagnostic) :
    expressionAtom literalExpression emptyBlock (overshot prior) = .reject eofFailure (overshot prior) ∧
    expressionAtom literalExpression emptyBlock (hidden prior) = .reject eofFailure (hidden prior) := by
  constructor
  · rw [expressionAtom, absent_core (overshot prior) rfl]
    rfl
  · rw [expressionAtom, absent_core (hidden prior) rfl]
    rfl

/-- The numerical gap is not a boundary. Public recovery commits the core
report once, then fails on its mandatory first token; its terminal report is
not emitted a second time and all non-diagnostic State fields remain exact. -/
theorem missing_backing_commits_one_report (prior : List ParseDiagnostic) :
    expressionAtomCore literalExpression emptyBlock (missing prior) = .reject eofFailure (missing prior) ∧
    expressionAtom literalExpression emptyBlock (missing prior) =
      .reject eofFailure ((missing prior).emit eofFailure.toDiagnostic) ∧
    ((missing prior).emit eofFailure.toDiagnostic).diagnostics = prior ++ [eofFailure.toDiagnostic] := by
  refine ⟨?_, ?_, ?_⟩
  · exact absent_core (missing prior) rfl
  · rw [expressionAtom, absent_core (missing prior) rfl]
    rfl
  · simp only [State.emit, State.diagnostics, missing, fixture, List.reverse_cons, List.reverse_reverse]

private def sym (first last : Nat) (kind : Symbol) : Token := {
  span := span first last, value := .symbol kind
}
private def literal42 : Expr := { span := numeral.span, value := .literal { span := numeral.span, value := .decimal "42" } }
private def groupTokens : Array Token := #[sym 0 1 .leftParen, numeral, sym 4 5 .rightParen]
private def tupleTokens : Array Token := #[sym 0 1 .leftParen, numeral, sym 4 5 .comma, numeral, sym 8 9 .rightParen]
private def rem (tokens : Array Token) (cursor : Nat) : Remainder := { tokens, cursor, endIndex := 9 }
private def groupValue : Expr := { span := span 0 5, value := .group literal42 }
private def tupleValue : Expr := {
  span := span 0 9, value := .tuple { span := span 0 9, elements := [literal42, literal42] }
}

private theorem parenthesized_exec {input : State} {value : Expr} {after : Remainder}
    (parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses input.file.id
      input.window.endByte input.declarativeRemainder value after []) :
    parenthesized literalExpression input = .ok value (input.traceResult after []) := by
  rcases parenthesized_trace_success_complete literalExpression_trace_success_complete
      literalExpression_success_context parsed with ⟨output, result, afterEq, events⟩
  have frame := parenthesized_success_context literalExpression_success_context result
  exact State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events ▸ result

private theorem group_parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses source 99
    (rem groupTokens 0) groupValue (rem groupTokens 3) [] :=
  .group (span 0 1) (span 4 5) (afterOpening := rem groupTokens 1) (afterElement := rem groupTokens 2)
    ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rem, groupTokens, numeral])
    ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
    (by simp [TokenKindAbsentAt, TokenAt, rem, groupTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩

private theorem tuple_parsed : ParenthesizedExpressionTraceParses LiteralExpressionTraceParses source 99
    (rem tupleTokens 0) tupleValue (rem tupleTokens 5) [] :=
  .tuple (span 0 1) (span 8 9) (afterOpening := rem tupleTokens 1) (afterFirst := rem tupleTokens 2)
    (first := literal42) (rest := [literal42]) (headEvents := []) (tailEvents := [])
    ⟨⟨by decide, rfl⟩, rfl⟩
    (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, numeral])
    ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
    (.final (span 4 5) (span 8 9) (afterComma := rem tupleTokens 3) (afterElement := rem tupleTokens 4)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, numeral])
      ⟨.parsed (.decimal ⟨by decide, rfl⟩), rfl⟩ (by decide)
      (by simp [TokenKindAbsentAt, TokenAt, rem, tupleTokens, sym]) ⟨⟨by decide, rfl⟩, rfl⟩)

/-- Actual group and two-element tuple successes are derived from independent
token judgments. Their impossible source/window bounds and prior events are
retained in the whole Reply; no complete-parser decision procedure is used. -/
theorem malformed_groups_and_tuples_still_succeed (prior : List ParseDiagnostic) :
    parenthesized literalExpression (fixture groupTokens 0 9 prior) =
      .ok groupValue (fixture groupTokens 3 9 prior) ∧
    parenthesized literalExpression (fixture tupleTokens 0 9 prior) =
      .ok tupleValue (fixture tupleTokens 5 9 prior) :=
  ⟨parenthesized_exec (input := fixture groupTokens 0 9 prior) group_parsed,
    parenthesized_exec (input := fixture tupleTokens 0 9 prior) tuple_parsed⟩

/-- Even without backing storage, all raw collection branches have ordinary
outcomes under the displayed numerical fuel budget. -/
theorem missing_backing_raw_branches_ordinary (prior : List ParseDiagnostic) :
    OrdinaryAt (parenthesized literalExpression) (missing prior) ∧
    OrdinaryAt (arrayLiteral literalExpression) (missing prior) ∧
    OrdinaryAt (dotConstructor literalExpression) (missing prior) :=
  literal_raw_branches_ordinary 3 (missing prior) (by change 3 < 4; decide)

end Solcore.Test.SyntaxExpressionAtomTotalityProperties
