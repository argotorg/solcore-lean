import Solcore.Syntax.DeclarativeExpressionAtomDispatchTraceProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! A stationary child satisfies all five exact trace contracts and ordinary
execution, but not strict progress. A selected parenthesized atom therefore
exposes noProgress, and completeness rules out either independent trace outcome.
Joint uniqueness and disjointness are deliberately not treated as existence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomTraceProgressProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def stationary {α : Type} (fixed : α) : Parser α := fun input => .ok fixed input
private def stationaryTrace {α : Type} (fixed : α) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (value : α) (after : Remainder) (trace : List ParseDiagnostic) : Prop :=
  value = fixed ∧ after = input ∧ trace = []
private def neverReject (_source : SourceId) (_endByte : Nat) (_input _after : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

private theorem stationary_sound {α : Type} (fixed : α) :
    ParserTraceSuccessSound (stationary fixed) (stationaryTrace fixed) := by
  intro input output value result
  change Reply.ok fixed input = .ok value output at result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm⟩

private theorem stationary_complete {α : Type} (fixed : α) :
    ParserTraceSuccessComplete (stationary fixed) (stationaryTrace fixed) := by
  intro input value after trace parsed
  rcases parsed with ⟨rfl, rfl, rfl⟩
  exact ⟨input, rfl, rfl, (List.append_nil _).symm⟩

private theorem stationary_frame {α : Type} (fixed : α) :
    ParserSuccessContext (stationary fixed) := by
  intro input output value result
  change Reply.ok fixed input = .ok value output at result
  cases result
  exact ⟨rfl, rfl⟩

private theorem stationary_reject_sound {α : Type} (fixed : α) :
    ParserTraceRejectSound (stationary fixed) neverReject := by
  intro input rejected failure result
  change Reply.ok fixed input = .reject failure rejected at result
  cases result

private theorem stationary_reject_complete {α : Type} (fixed : α) :
    ParserTraceRejectComplete (stationary fixed) neverReject := by
  intro input after report trace impossible
  exact False.elim impossible

private theorem stationary_exact {α : Type} (fixed : α) (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (stationaryTrace fixed) neverReject source endByte where
  successResultUnique := by
    rintro input left right afterLeft afterRight leftTrace rightTrace
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intros; contradiction
  successRejectDisjoint := by intros; contradiction

/-- These are genuine contracts over every State, not just the fixture below. -/
theorem stationary_child_has_five_contracts_and_is_ordinary {α : Type} (fixed : α) :
    ParserTraceSuccessSound (stationary fixed) (stationaryTrace fixed) ∧
    ParserTraceSuccessComplete (stationary fixed) (stationaryTrace fixed) ∧
    ParserSuccessContext (stationary fixed) ∧
    ParserTraceRejectSound (stationary fixed) neverReject ∧
    ParserTraceRejectComplete (stationary fixed) neverReject ∧
    Parser.Ordinary (stationary fixed) :=
  ⟨stationary_sound fixed, stationary_complete fixed, stationary_frame fixed,
    stationary_reject_sound fixed, stationary_reject_complete fixed,
    fun input => .inl ⟨fixed, input, rfl⟩⟩

private def source : SourceId := { origin := .main, path := "stationary-atom.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def tokens : Array Token := #[token 0 1 .leftParen, token 1 2 .plus, token 2 3 .rightParen]
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "(+)" }, tokens, cursor := 0
  window := { endIndex := 3, endByte := 3 }, diagnosticsRev := prior.reverse
}
private def fixed : Expr := { span := span 1 2, value := .error }
private def fixedBlock : Block := { span := span 0 3, value := [] }

private theorem parenthesized_selected (prior : List ParseDiagnostic) :
    ExpressionAtomDispatchSelects (input prior).declarativeRemainder .parenthesized := by
  constructor <;>
    simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt,
      input, State.declarativeRemainder, tokens, token]

/-- The child succeeds while leaving the plus token and all State fields intact. -/
theorem successful_child_has_zero_progress (prior : List ParseDiagnostic) :
    stationary fixed { input prior with cursor := 1 } =
      .ok fixed { input prior with cursor := 1 } ∧
    ¬ (1 : Nat) < ({ input prior with cursor := 1 } : State).cursor :=
  ⟨rfl, Nat.lt_irrefl 1⟩

/-- Exact token execution and the selected raw branch expose the progress check;
no evaluation tactic is applied to the complete atom parser. -/
theorem stationary_atom_reaches_noProgress (block : Parser Block) (prior : List ParseDiagnostic) :
    expressionAtomCore (stationary fixed) block (input prior) =
      .invariant (.noProgress .expression (span 1 2)) := by
  have opening : ExactTokenParses (.symbol .leftParen) (input prior).declarativeRemainder
      (span 0 1) { (input prior).declarativeRemainder with cursor := 1 } :=
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
  have closeAbsent : isSymbol ({ input prior with cursor := 1 } : State) .rightParen = false :=
    DelimitedTraceInternals.symbol_absent .rightParen (by
      simp [TokenKindAbsentAt, TokenAt, input, tokens, token])
  rw [expressionAtomCore_eq_raw_of_selection (stationary fixed) block (parenthesized_selected prior)]
  change parenthesized (stationary fixed) (input prior) = _
  rw [parenthesized, symbol_eq_ok_of_exactTokenParses .leftParen .expression opening]
  simp only [show (input prior).cursor + 1 = 1 from rfl, closeAbsent, Bool.false_eq_true,
    if_false, stationary, Nat.le_refl, if_true]
  rfl

/-- Both children have independent exact joint bundles, so the atom layer does
too. This is compatible with having no trace outcome at the fixture. -/
theorem stationary_dispatch_has_exact_joint (sourceId : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec
      (ExpressionAtomDispatchTraceParses (stationaryTrace fixed) (stationaryTrace fixedBlock))
      (ExpressionAtomDispatchTraceRejects (stationaryTrace fixed) neverReject neverReject) sourceId endByte :=
  expressionAtomDispatchTraceExactOutcomeSpec
    (stationary_exact fixed sourceId endByte) (stationary_exact fixedBlock sourceId endByte)

/-- The direction from grammar to execution, not vacuous execution soundness,
excludes both successes and rejections at this noProgress input. -/
theorem stationary_dispatch_has_no_trace_outcome (prior : List ParseDiagnostic) :
    (¬ ∃ value after trace, ExpressionAtomDispatchTraceParses (stationaryTrace fixed)
      (stationaryTrace fixedBlock) source 3 (input prior).declarativeRemainder value after trace) ∧
    (¬ ∃ after report trace, ExpressionAtomDispatchTraceRejects (stationaryTrace fixed)
      neverReject neverReject source 3 (input prior).declarativeRemainder after report trace) := by
  constructor
  · rintro ⟨value, after, trace, parsed⟩
    rcases expressionAtomCore_trace_success_complete (stationary_complete fixed)
      (stationary_frame fixed) (stationary_complete fixedBlock) (input := input prior) parsed with ⟨output, result, _⟩
    rw [stationary_atom_reaches_noProgress] at result
    contradiction
  · rintro ⟨after, report, trace, rejection⟩
    rcases expressionAtomCore_trace_reject_complete (stationary_complete fixed)
      (stationary_reject_complete fixed) (stationary_frame fixed)
      (stationary_reject_complete fixedBlock) (input := input prior) rejection with ⟨failure, rejected, result, _⟩
    rw [stationary_atom_reaches_noProgress] at result
    contradiction

theorem stationary_atom_is_not_ordinary (block : Parser Block) :
    ¬ Parser.Ordinary (expressionAtomCore (stationary fixed) block) := by
  intro ordinary
  exact ordinary.ne_invariant (input []) (.noProgress .expression (span 1 2))
    (stationary_atom_reaches_noProgress block [])

end Solcore.Test.SyntaxExpressionAtomTraceProgressProperties
