import Solcore.Syntax.Parser.TypeExprTraceUnrestrictedProperties
import Solcore.Syntax.Parser.TypeExprTraceExistenceProperties
import Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

/-! Reverse recursive correspondence on intentionally noncanonical states.
The carrier is shorter than its active window, token provenance is malformed,
and the source is empty. Separate missing-carrier and past-window failures
retain the complete state and leave their EOF report uncommitted. No complete
parser evaluation or input-validity assumption is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceUnrestrictedExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

private def source : SourceId := { origin := .main, path := "unrestricted-type.sol" }
private def alien : SourceId := { origin := .main, path := "unrelated-token.sol" }
private def file : SourceFile := { id := source, content := "" }
private def name : Identifier := {
  span := { source := alien, startByte := 50, endByte := 2 }, value := "a-b"
}
private def token : Token := { span := name.span, value := .identifier name.value }
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def value : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def state (prior : List ParseDiagnostic) (cursor : Nat) : State := {
  file, tokens := #[token], cursor, window := { endIndex := 3, endByte := 99 }
  diagnosticsRev := prior.reverse
}
private def advanced (prior : List ParseDiagnostic) : State := {
  state prior 1 with diagnosticsRev := [event] ++ prior.reverse
}
private def failure : Failure := {
  span := { source, startByte := 99, endByte := 99 }, found := none
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

theorem noncanonical_state (prior : List ParseDiagnostic) (cursor : Nat) :
    name.span.source ≠ (state prior cursor).file.id ∧ name.span.endByte < name.span.startByte ∧
      (state prior cursor).tokens.size < (state prior cursor).window.endIndex ∧
      (state prior cursor).file.content.utf8ByteSize < (state prior cursor).window.endByte ∧
      ¬ (state prior cursor).ValidFor := by
  refine ⟨by change alien ≠ source; decide, by decide,
    by change 1 < 3; decide, by change 0 < 99; decide, ?_⟩
  intro valid
  have bound := valid.endIndex_le_size
  change 3 ≤ 1 at bound
  omega

theorem noncanonical_ordinary_and_noInvariant (prior : List ParseDiagnostic) (cursor : Nat) :
    ((∃ result next, typeExpr (state prior cursor) = .ok result next) ∨
      (∃ error next, typeExpr (state prior cursor) = .reject error next)) ∧
      ∀ error, typeExpr (state prior cursor) ≠ .invariant error :=
  ⟨typeExpr_ordinary (state prior cursor), typeExpr_ne_invariant_unrestricted (state prior cursor)⟩

theorem noncanonical_execution_with_trace (prior : List ParseDiagnostic) (cursor : Nat) :
    (∃ result output trace, typeExpr (state prior cursor) = .ok result output ∧
      TypeExprTraceParses source 99 (state prior cursor).declarativeRemainder
        result output.declarativeRemainder trace ∧ output.diagnostics = prior ++ trace) ∨
    (∃ error rejected trace, typeExpr (state prior cursor) = .reject error rejected ∧
      TypeExprTraceRejects source 99 (state prior cursor).declarativeRemainder
        rejected.declarativeRemainder error.toDiagnostic trace ∧ rejected.diagnostics = prior ++ trace) := by
  rcases typeExpr_exists_trace_outcome (state prior cursor) with
    ⟨result, output, trace, executed, parsed, events⟩ | ⟨error, rejected, trace, executed, rejection, events⟩
  · refine .inl ⟨result, output, trace, executed, parsed, ?_⟩
    simpa only [state, State.diagnostics, List.reverse_reverse] using events
  · refine .inr ⟨error, rejected, trace, executed, rejection, ?_⟩
    simpa only [state, State.diagnostics, List.reverse_reverse] using events

private theorem malformed_leaf_trace (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 99 (state prior 0).declarativeRemainder value
      (state prior 1).declarativeRemainder [event] := by
  have tokenAt : TokenAt (state prior 0).tokens (state prior 0).window.endIndex (state prior 0).cursor token :=
    ⟨by change 0 < 3; decide, rfl⟩
  have noDot : TokenKindAbsentAt (state prior 1).tokens (state prior 1).window.endIndex
      (state prior 1).cursor (.symbol .dot) := by simp [TokenKindAbsentAt, TokenAt, state]
  have noArguments : TokenKindAbsentAt (state prior 1).tokens (state prior 1).window.endIndex
      (state prior 1).cursor (.symbol .less) := by simp [TokenKindAbsentAt, TokenAt, state]
  have head : IdentifierTraceParses (state prior 0).declarativeRemainder name
      (state prior 1).declarativeRemainder [event] :=
    .parsed ⟨tokenAt, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
  have qualified : QualifiedNameTraceParses source 99 (state prior 0).declarativeRemainder
      (tracedQualifiedName name []) (state prior 1).declarativeRemainder [event] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head
      (DottedIdentifierTailTraceParses.done noDot)
  have raw : NamedTypeTraceParses TypeExprTraceParses source 99 (state prior 0).declarativeRemainder
      value (state prior 1).declarativeRemainder [event] := by
    simpa only [List.append_nil, value] using NamedTypeTraceParses.parsed qualified
      (NamedTypeArgumentsTraceParses.absent noArguments)
      (NamedTypeFinishingTrace.ordinary (by
        unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix name
        decide))
  exact TypeExprTraceParses.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 0) = .named from rfl)) raw)

theorem malformed_leaf_reconstructed (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 99 (state prior 0).declarativeRemainder value
      (state prior 1).declarativeRemainder [event] ∧
      ∃ output, typeExpr (state prior 0) = .ok value output ∧ output = advanced prior ∧
        output.declarativeRemainder = (state prior 1).declarativeRemainder ∧
        output.diagnostics = prior ++ [event] ∧ output.file = file ∧
        output.window = { endIndex := 3, endByte := 99 } := by
  have parsed := malformed_leaf_trace prior
  rcases (typeExpr_trace_success_iff (input := state prior 0)).mp parsed with ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 0) = .ok value (advanced prior) :=
    checked_name_type (input := state prior 0) (name := name) (trace := [event])
      ⟨by change 0 < 3; decide, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
      (by simp [TokenKindAbsentAt, TokenAt, state])
      (by simp [TokenKindAbsentAt, TokenAt, state]) (by decide) (by decide)
  rw [componentResult] at result
  cases result
  refine ⟨parsed, _, componentResult, rfl, afterEq, ?_, rfl, rfl⟩
  simpa only [state, State.diagnostics, List.reverse_reverse] using events

private theorem missing_carrier_trace (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 99 (state prior 1).declarativeRemainder
      (state prior 1).declarativeRemainder failure.toDiagnostic [] :=
  TypeExprTraceRejects.roll (.selected .final
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 1) = .final from rfl))
    (.rejected (.reported (.missingToken (by change 1 < 3; decide) rfl))))

theorem missing_carrier_reconstructed (prior : List ParseDiagnostic) :
    (state prior 1).cursor < (state prior 1).window.endIndex ∧ (state prior 1).tokens[1]? = none ∧
      TypeExprTraceRejects source 99 (state prior 1).declarativeRemainder
        (state prior 1).declarativeRemainder failure.toDiagnostic [] ∧
      ∃ output, typeExpr (state prior 1) = .reject failure output ∧ output = state prior 1 ∧
        output.declarativeRemainder = (state prior 1).declarativeRemainder ∧ output.diagnostics = prior := by
  have rejected := missing_carrier_trace prior
  rcases (typeExpr_trace_reject_failure_iff (input := state prior 1)).mp rejected with
    ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 1) = .reject failure (state prior 1) := by
    change typeExprWithFuel ((state prior 1).remainingCount + 1) (state prior 1) = _
    rw [typeExprWithFuel_eq_raw_of_selection (state prior 1).remainingCount
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state prior 1) = .final from rfl))]
    rfl
  rw [componentResult] at result
  cases result
  refine ⟨by change 1 < 3; decide, rfl, rejected, _, componentResult, rfl, afterEq, ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

private theorem past_window_trace (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 99 (state prior 7).declarativeRemainder
      (state prior 7).declarativeRemainder failure.toDiagnostic [] :=
  TypeExprTraceRejects.roll (.selected .final
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 7) = .final from rfl))
    (.rejected (.reported (.windowEnd (by change 3 ≤ 7; decide)))))

theorem past_window_reconstructed (prior : List ParseDiagnostic) :
    (state prior 7).window.endIndex < (state prior 7).cursor ∧
      TypeExprTraceRejects source 99 (state prior 7).declarativeRemainder
        (state prior 7).declarativeRemainder failure.toDiagnostic [] ∧
      ∃ output, typeExpr (state prior 7) = .reject failure output ∧ output = state prior 7 ∧
        output.declarativeRemainder = (state prior 7).declarativeRemainder ∧ output.diagnostics = prior := by
  have rejected := past_window_trace prior
  rcases (typeExpr_trace_reject_failure_iff (input := state prior 7)).mp rejected with
    ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 7) = .reject failure (state prior 7) := by
    change typeExprWithFuel ((state prior 7).remainingCount + 1) (state prior 7) = _
    rw [typeExprWithFuel_eq_raw_of_selection (state prior 7).remainingCount
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state prior 7) = .final from rfl))]
    rfl
  rw [componentResult] at result
  cases result
  refine ⟨by change 3 < 7; decide, rejected, _, componentResult, rfl, afterEq, ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxTypeExprTraceUnrestrictedExamples
