import Solcore.Syntax.Parser.TypeExprTraceStateProperties

/-! Independent nested traces reconstruct whole replies with arbitrary prior
events. Separate counterexamples show why cursor-only equality cannot replace
the full-state iff when a proposed remainder has a different token carrier or
end index. No complete parser evaluation is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceStateProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "whole-type-state.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def atToken : Token := { span := span 0 1, value := .symbol .at }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def successTokens : List Token := [atToken, nameToken, { span := span 4 5, value := .symbol .semicolon }]
private def rejectTokens : List Token := [atToken, nameToken,
  { span := span 4 5, value := .symbol .dot }, { span := span 5 6, value := .symbol .plus }]
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}
private def input (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := text }, tokens := tokens.toArray, cursor := 0
  window := { endIndex := tokens.length, endByte := text.utf8ByteSize }, diagnosticsRev := prior.reverse
}
private def leaf : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def value : TypeExpr := { span := SourceSpan.cover (span 0 1) leaf.span, value := .proxy (span 0 1) leaf }
private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .typeExpr
}
private def successfulState (prior : List ParseDiagnostic) : State := {
  input "@a-b;" successTokens prior with cursor := 2, diagnosticsRev := [event] ++ prior.reverse
}
private def rejectedState (prior : List ParseDiagnostic) : State := {
  input "@a-b.+" rejectTokens prior with cursor := 3, diagnosticsRev := [event] ++ prior.reverse
}

private theorem head_trace (tokens : List Token)
    (present : TokenAt tokens.toArray tokens.length 1 nameToken) :
    IdentifierTraceParses (remainder tokens 1) name (remainder tokens 2) [event] :=
  .parsed ⟨present, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))

private theorem success_trace :
    TypeExprTraceParses source 5 (remainder successTokens 0) value (remainder successTokens 2) [event] := by
  have head := head_trace successTokens ⟨by change 1 < 3; decide, rfl⟩
  have noDot : TokenKindAbsentAt successTokens.toArray successTokens.length 2 (.symbol .dot) := by
    simp [TokenKindAbsentAt, TokenAt, successTokens]
  have noArguments : TokenKindAbsentAt successTokens.toArray successTokens.length 2 (.symbol .less) := by
    simp [TokenKindAbsentAt, TokenAt, successTokens]
  have qualified : QualifiedNameTraceParses source 5 (remainder successTokens 1)
      (tracedQualifiedName name []) (remainder successTokens 2) [event] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head (DottedIdentifierTailTraceParses.done noDot)
  have named : NamedTypeTraceParses TypeExprTraceParses source 5 (remainder successTokens 1)
      leaf (remainder successTokens 2) [event] := by
    simpa only [List.append_nil, leaf] using NamedTypeTraceParses.parsed qualified
      (NamedTypeArgumentsTraceParses.absent noArguments)
      (NamedTypeFinishingTrace.ordinary (by
        unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix name
        decide))
  have child := TypeExprTraceParses.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch { input "@a-b;" successTokens [] with cursor := 1 } = .named from rfl)) named)
  have proxy : ProxyTypeTraceParses TypeExprTraceParses source 5 (remainder successTokens 0)
      value (remainder successTokens 2) [event] := by
    unfold value
    exact .parsed (span 0 1) ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩ child
  exact TypeExprTraceParses.roll (.selected .proxy
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (input "@a-b;" successTokens []) = .proxy from rfl))
    proxy)

private theorem rejection_trace :
    TypeExprTraceRejects source 6 (remainder rejectTokens 0) (remainder rejectTokens 3)
      failure.toDiagnostic [event] := by
  have head := head_trace rejectTokens ⟨by change 1 < 4; decide, rfl⟩
  have tail : DottedIdentifierTailTraceRejects .typeExpr source 6 (remainder rejectTokens 2)
      (remainder rejectTokens 3) failure.toDiagnostic [] :=
    .componentRejected (span 4 5) ⟨⟨by change 2 < 4; decide, rfl⟩, rfl⟩
      (by simp [IdentifierAbsentAt, TokenAt, remainder, rejectTokens])
      (.reported (.token (current := { span := span 5 6, value := .symbol .plus })
        ⟨by change 3 < 4; decide, rfl⟩))
  have named : NamedTypeTraceRejects TypeExprTraceParses TypeExprTraceRejects source 6
      (remainder rejectTokens 1) (remainder rejectTokens 3) failure.toDiagnostic [event] := by
    exact .nameRejected (by simpa only [List.append_nil] using QualifiedNameTraceRejects.tailRejected head tail)
  have child := TypeExprTraceRejects.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch { input "@a-b.+" rejectTokens [] with cursor := 1 } = .named from rfl)) named)
  exact TypeExprTraceRejects.roll (.selected .proxy
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (input "@a-b.+" rejectTokens []) = .proxy from rfl))
    (.innerRejected (span 0 1) ⟨⟨by change 0 < 4; decide, rfl⟩, rfl⟩ child))

theorem nested_success_whole_state (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 5 (remainder successTokens 0) value (remainder successTokens 2) [event] ∧
    typeExpr (input "@a-b;" successTokens prior) = .ok value (successfulState prior) ∧
    (successfulState prior).diagnostics = prior ++ [event] ∧
    (successfulState prior).peek? = some { span := span 4 5, value := .symbol .semicolon } := by
  refine ⟨success_trace, ?_, ?_, rfl⟩
  · exact (typeExpr_trace_success_state_iff (input := input "@a-b;" successTokens prior)).mp success_trace
  · simp only [successfulState, State.diagnostics, List.reverse_append, List.reverse_reverse, List.reverse_singleton]

theorem nested_rejection_whole_state (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 6 (remainder rejectTokens 0) (remainder rejectTokens 3) failure.toDiagnostic [event] ∧
    typeExpr (input "@a-b.+" rejectTokens prior) = .reject failure (rejectedState prior) ∧
    (rejectedState prior).diagnostics = prior ++ [event] ∧
    (rejectedState prior).peek? = some { span := span 5 6, value := .symbol .plus } := by
  refine ⟨rejection_trace, ?_, ?_, rfl⟩
  · exact (typeExpr_trace_reject_failure_state_iff (input := input "@a-b.+" rejectTokens prior)).mp rejection_trace
  · simp only [rejectedState, State.diagnostics, List.reverse_append, List.reverse_reverse, List.reverse_singleton]

theorem nested_report_whole_state (prior : List ParseDiagnostic) :
    ∃ actual, typeExpr (input "@a-b.+" rejectTokens prior) = .reject actual (rejectedState prior) ∧
      actual.toDiagnostic = failure.toDiagnostic ∧ actual = failure := by
  rcases (typeExpr_trace_reject_state_iff (input := input "@a-b.+" rejectTokens prior)).mp rejection_trace with
    ⟨actual, result, same⟩
  exact ⟨actual, result, same, Failure.toDiagnostic_injective same⟩

private def wrongTokens : Remainder := { remainder successTokens 2 with tokens := #[] }
private def wrongEndIndex : Remainder := { remainder successTokens 2 with endIndex := 0 }

/-- Cursor-only equality stays true even though the proposed carrier cannot be an outcome. -/
theorem cursor_only_forgets_tokens (prior : List ParseDiagnostic) :
    typeExpr (input "@a-b;" successTokens prior) = .ok value
      { input "@a-b;" successTokens prior with
        cursor := wrongTokens.cursor
        diagnosticsRev := [event] ++ prior.reverse } ∧
    ¬ TypeExprTraceParses source 5 (remainder successTokens 0) value wrongTokens [event] ∧
    (input "@a-b;" successTokens prior).traceResult wrongTokens [event] ≠ successfulState prior := by
  refine ⟨(nested_success_whole_state prior).2.1, ?_, ?_⟩
  · intro wrong
    have tokenEq := congrArg Remainder.tokens (wrong.result_unique success_trace).2.1
    have sizes := congrArg Array.size tokenEq
    change 0 = 3 at sizes
    contradiction
  · intro same
    have sizes := congrArg (fun state : State => state.tokens.size) same
    change 0 = 3 at sizes
    contradiction

/-- The same issue occurs independently for a mismatched end index. -/
theorem cursor_only_forgets_endIndex (prior : List ParseDiagnostic) :
    typeExpr (input "@a-b;" successTokens prior) = .ok value
      { input "@a-b;" successTokens prior with
        cursor := wrongEndIndex.cursor
        diagnosticsRev := [event] ++ prior.reverse } ∧
    ¬ TypeExprTraceParses source 5 (remainder successTokens 0) value wrongEndIndex [event] ∧
    (input "@a-b;" successTokens prior).traceResult wrongEndIndex [event] ≠ successfulState prior := by
  refine ⟨(nested_success_whole_state prior).2.1, ?_, ?_⟩
  · intro wrong
    have indexes := congrArg Remainder.endIndex (wrong.result_unique success_trace).2.1
    change 0 = 3 at indexes
    contradiction
  · intro same
    have indexes := congrArg (fun state : State => state.window.endIndex) same
    change 0 = 3 at indexes
    contradiction

end Solcore.Test.SyntaxTypeExprTraceStateProperties
