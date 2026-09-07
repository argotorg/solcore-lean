import Solcore.Syntax.Parser.TypeDispatchSelectionTraceProperties
import Solcore.Test.SyntaxCanonicalDelimitedTrailingTraceExamples

/-! Boundary consumers of the real positive-fuel dispatcher. Token-carrier
fixtures deliberately need no source-validity law; the active window, not the
backing array, controls contextual pairs. Only finite lexing is evaluated. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.TypeDispatchTraceInternals

private def source : SourceId := { origin := .main, path := "type-dispatch-trace.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def token (kind : TokenKind) : Token := { span := span 0 1, value := kind }
private def state (kinds : List TokenKind) (endIndex : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }
  tokens := (kinds.map token).toArray
  cursor := 0
  window := { endIndex, endByte := 99 }
  diagnosticsRev := prior.reverse
}

private theorem runs_selected (fuel : Nat) {input : State} {branch : TypeDispatchBranch}
    (selected : selectedBranch input = branch) :
    typeExprWithFuel (fuel + 1) input = rawParser (typeExprWithFuel fuel) branch input :=
  typeExprWithFuel_eq_raw_of_selection fuel (selectedBranch_eq_iff.mp selected)

theorem function_keyword_and_identifier_are_distinct (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.keyword .functionKw] 1 prior) = .function ∧
    selectedBranch (state [.identifier "function"] 1 prior) = .named ∧
    typeExprWithFuel (fuel + 1) (state [.keyword .functionKw] 1 prior) =
      parseFunctionType (typeExprWithFuel fuel) (state [.keyword .functionKw] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "function"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "function"] 1 prior) := by
  exact ⟨rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem mapping_requires_its_left_parenthesis (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.identifier "mapping"] 1 prior) = .named ∧
    selectedBranch (state [.identifier "mapping", .symbol .less] 2 prior) = .named ∧
    selectedBranch (state [.identifier "mapping", .symbol .leftParen] 2 prior) = .mapping ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping"] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .less] 2 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .less] 2 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .leftParen] 2 prior) =
      parseMappingType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .leftParen] 2 prior) := by
  exact ⟨rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem comptime_requires_its_angle (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.identifier "comptime"] 1 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .leftParen] 2 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .less] 2 prior) = .comptime ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime"] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime"] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .leftParen] 2 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .leftParen] 2 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .less] 2 prior) =
      parseComptimeType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .less] 2 prior) := by
  exact ⟨rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem proxy_and_tuple_have_their_own_branches (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.symbol .at] 1 prior) = .proxy ∧
    selectedBranch (state [.symbol .leftParen] 1 prior) = .tuple ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .at] 1 prior) =
      parseProxyType (typeExprWithFuel fuel) (state [.symbol .at] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .leftParen] 1 prior) =
      parseTupleType (typeExprWithFuel fuel) (state [.symbol .leftParen] 1 prior) := by
  exact ⟨rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem hidden_second_tokens_do_not_select_pairs (fuel : Nat) (prior : List ParseDiagnostic) :
    (state [.identifier "mapping", .symbol .leftParen] 1 prior).tokens[1]? = some (token (.symbol .leftParen)) ∧
    (state [.identifier "comptime", .symbol .less] 1 prior).tokens[1]? = some (token (.symbol .less)) ∧
    (state [.identifier "mapping", .symbol .leftParen] 1 prior).peekOffsetKind? 1 = none ∧
    (state [.identifier "comptime", .symbol .less] 1 prior).peekOffsetKind? 1 = none ∧
    selectedBranch (state [.identifier "mapping", .symbol .leftParen] 1 prior) = .named ∧
    selectedBranch (state [.identifier "comptime", .symbol .less] 1 prior) = .named ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "mapping", .symbol .leftParen] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "mapping", .symbol .leftParen] 1 prior) ∧
    typeExprWithFuel (fuel + 1) (state [.identifier "comptime", .symbol .less] 1 prior) =
      parseNamedType (typeExprWithFuel fuel) (state [.identifier "comptime", .symbol .less] 1 prior) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, runs_selected fuel rfl, runs_selected fuel rfl⟩

theorem final_selection_keeps_complete_state (fuel : Nat) {input : State}
    (selection : TypeDispatchSelects input.declarativeRemainder .final) :
    typeExprWithFuel (fuel + 1) input = .reject {
      span := input.currentSpan, found := input.peekKind?
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } input := by
  rw [typeExprWithFuel_eq_raw_of_selection fuel selection]
  rfl

theorem unexpected_token_reports_without_commit (fuel : Nat) (prior : List ParseDiagnostic) :
    selectedBranch (state [.symbol .plus] 1 prior) = .final ∧
    typeExprWithFuel (fuel + 1) (state [.symbol .plus] 1 prior) = .reject {
      span := span 0 1, found := some (.symbol .plus)
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } (state [.symbol .plus] 1 prior) ∧
    (state [.symbol .plus] 1 prior).diagnostics = prior := by
  refine ⟨rfl, final_selection_keeps_complete_state fuel (selectedBranch_eq_iff.mp rfl), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

theorem hidden_current_token_reports_window_end (fuel : Nat) (prior : List ParseDiagnostic) :
    (state [.keyword .functionKw] 0 prior).tokens[0]? = some (token (.keyword .functionKw)) ∧
    selectedBranch (state [.keyword .functionKw] 0 prior) = .final ∧
    typeExprWithFuel (fuel + 1) (state [.keyword .functionKw] 0 prior) = .reject {
      span := span 99 99, found := none
      expected := { head := .typeExpr, tail := [] }, context := .typeExpr
    } (state [.keyword .functionKw] 0 prior) ∧
    (state [.keyword .functionKw] 0 prior).diagnostics = prior := by
  refine ⟨rfl, rfl, final_selection_keeps_complete_state fuel (selectedBranch_eq_iff.mp rfl), ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

private def canonicalFile : SourceFile := { id := source, content := "mapping(" }
private def canonicalLexed : LexedFile := {
  source, tokens := [
    { span := span 0 7, value := .identifier "mapping" },
    { span := span 7 8, value := .symbol .leftParen }
  ], comments := [], diagnostics := []
}

set_option maxRecDepth 16384 in
theorem canonical_mapping_prefix_lexes_and_selects (fuel : Nat) (prior : List ParseDiagnostic) :
    Lexer.lex canonicalFile = .ok canonicalLexed ∧
    selectedBranch { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } = .mapping ∧
    typeExprWithFuel (fuel + 1) { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } =
      parseMappingType (typeExprWithFuel fuel)
        { State.initial canonicalFile canonicalLexed with diagnosticsRev := prior.reverse } := by
  refine ⟨?_, rfl, runs_selected fuel rfl⟩
  apply SyntaxCanonicalDelimitedTrailingTraceExamples.lex_ok_of_toOption
  decide +kernel

end Solcore.Test.SyntaxTypeDispatchTraceProperties
