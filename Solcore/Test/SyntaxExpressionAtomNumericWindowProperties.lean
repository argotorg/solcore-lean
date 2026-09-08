import Solcore.Syntax.Parser.ExpressionAtomUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchRejectionContextProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchTraceCorrespondenceProperties
import Solcore.Syntax.Parser.ExpressionAtomTraceStateProperties

/-! Both supplied children satisfy every three-field fuel contract, but a
rejected child can enlarge endIndex. Public atom recovery then succeeds with
that changed numeric window. The independent trace reconstructs the whole
reply without source-content validity or a rejected full-window frame. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxExpressionAtomNumericWindowProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "atom-numeric-window.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def tokens : Array Token := #[token 0 1 .leftParen, token 1 2 .plus, token 2 3 .semicolon]
private def before : Remainder := { tokens, cursor := 0, endIndex := 3 }
private def failed : Remainder := { before with cursor := 1, endIndex := 4 }
private def after : Remainder := { before with cursor := 2, endIndex := 4 }
private def input (text : String) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := text }, tokens, cursor := 0
  window := { endIndex := 3, endByte := 3 }, diagnosticsRev := prior.reverse
}
private def failure : Failure := {
  span := span 1 2, found := some (.symbol .plus)
  expected := { head := .expression, tail := [] }, context := .expression
}
private def errorValue : Expr := { span := span 0 2, value := .error }
private def recoveryEvent : ParseDiagnostic := expressionAtomRecoveryTraceEvent errorValue.span
private def rejectedRemainder (enlarge : Bool) (state : Remainder) : Remainder := {
  state with endIndex := if enlarge then 4 else state.endIndex
}
private def rejectedState (enlarge : Bool) (state : State) : State := {
  state with window := { state.window with endIndex := if enlarge then 4 else state.window.endIndex }
}
private def rejecting {α : Type} (enlarge : Bool) : Parser α := fun state =>
  .reject failure (rejectedState enlarge state)
private abbrev nested : Parser Expr := rejecting true
private abbrev block : Parser Block := rejecting false
private def neverSuccess {α : Type} (_source : SourceId) (_endByte : Nat) (_input : Remainder)
    (_value : α) (_after : Remainder) (_trace : List ParseDiagnostic) : Prop := False
private def childRejects (enlarge : Bool) (_source : SourceId) (_endByte : Nat)
    (state after : Remainder) (report : ParseDiagnostic) (trace : List ParseDiagnostic) : Prop :=
  after = rejectedRemainder enlarge state ∧ report = failure.toDiagnostic ∧ trace = []
private abbrev coreParses := ExpressionAtomDispatchTraceParses
  (neverSuccess (α := Expr)) (neverSuccess (α := Block))
private abbrev coreRejects := ExpressionAtomDispatchTraceRejects
  (neverSuccess (α := Expr)) (childRejects true) (childRejects false)
private def recovered (text : String) (prior : List ParseDiagnostic) : State := {
  input text prior with
  cursor := 2
  window := { endIndex := 4, endByte := 3 }
  diagnosticsRev := recoveryEvent :: failure.toDiagnostic :: prior.reverse
}

private theorem rejecting_success_sound {α : Type} (enlarge : Bool) :
    ParserTraceSuccessSound (rejecting (α := α) enlarge) neverSuccess := by
  intro state output value result
  cases result
private theorem rejecting_success_complete {α : Type} (enlarge : Bool) :
    ParserTraceSuccessComplete (rejecting (α := α) enlarge) neverSuccess := by
  intro state value after trace impossible
  exact False.elim impossible
private theorem rejecting_success_context {α : Type} (enlarge : Bool) :
    ParserSuccessContext (rejecting (α := α) enlarge) := by
  intro state output value result
  cases result
private theorem rejecting_reject_sound {α : Type} (enlarge : Bool) :
    ParserTraceRejectSound (rejecting (α := α) enlarge) (childRejects enlarge) := by
  intro state output actual result
  cases result
  exact ⟨[], ⟨rfl, rfl, rfl⟩, (List.append_nil _).symm⟩
private theorem rejecting_reject_complete {α : Type} (enlarge : Bool) :
    ParserTraceRejectComplete (rejecting (α := α) enlarge) (childRejects enlarge) := by
  rintro state after report trace ⟨rfl, rfl, rfl⟩
  exact ⟨failure, rejectedState enlarge state, rfl, rfl, rfl, (List.append_nil _).symm⟩
private theorem rejecting_reject_frame {α : Type} (enlarge : Bool)
    {state output : State} {actual : Failure} (result : rejecting (α := α) enlarge state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  cases result
  exact ⟨rfl, rfl⟩
private theorem rejecting_contract {α : Type} (enlarge : Bool) (fuel : Nat) :
    UnrestrictedFuelElementContract (rejecting (α := α) enlarge) fuel where
  endIndexOnSuccess result := by cases result
  cursorLtOnSuccess result := by cases result
  ordinary _ _ := .inr ⟨_, _, rfl⟩

private theorem core_success_sound : ParserTraceSuccessSound (expressionAtomCore nested block) coreParses :=
  expressionAtomCore_trace_success_sound (rejecting_success_sound true) (rejecting_success_context true)
    (rejecting_success_sound false)
private theorem core_success_complete : ParserTraceSuccessComplete (expressionAtomCore nested block) coreParses :=
  expressionAtomCore_trace_success_complete (rejecting_success_complete true) (rejecting_success_context true)
    (rejecting_success_complete false)
private theorem core_reject_sound : ParserTraceRejectSound (expressionAtomCore nested block) coreRejects :=
  expressionAtomCore_reject_trace_sound (rejecting_success_sound true) (rejecting_reject_sound true)
    (rejecting_success_context true) (rejecting_reject_sound false)
private theorem core_reject_complete : ParserTraceRejectComplete (expressionAtomCore nested block) coreRejects :=
  expressionAtomCore_trace_reject_complete (rejecting_success_complete true) (rejecting_reject_complete true)
    (rejecting_success_context true) (rejecting_reject_complete false)
private theorem core_success_frame {state output : State} {value : Expr}
    (result : expressionAtomCore nested block state = .ok value output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte := by
  have frame := expressionAtomCore_trace_success_context (rejecting_success_context true)
    (rejecting_success_context false) result
  exact ⟨frame.1, congrArg TokenWindow.endByte frame.2⟩
private theorem core_reject_frame {state output : State} {actual : Failure}
    (result : expressionAtomCore nested block state = .reject actual output) :
    output.file = state.file ∧ output.window.endByte = state.window.endByte :=
  expressionAtomCore_reject_source_endByte (rejecting_success_context true)
    (rejecting_reject_frame true) (rejecting_reject_frame false) result

theorem children_have_every_fuel_contract (fuel : Nat) :
    UnrestrictedFuelElementContract nested fuel ∧ UnrestrictedFuelElementContract block fuel :=
  ⟨rejecting_contract true fuel, rejecting_contract false fuel⟩

theorem nested_changes_only_rejected_endIndex {state output : State} {actual : Failure}
    (result : nested state = .reject actual output) :
    output.file = state.file ∧ output.tokens = state.tokens ∧ output.cursor = state.cursor ∧
    output.window.endByte = state.window.endByte ∧ output.diagnostics = state.diagnostics ∧
    output.window.endIndex = 4 := by
  cases result
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem selected : ExpressionAtomDispatchSelects before .parenthesized := by
  constructor <;> simp [CoreLiteralStartsAt, ExpressionNameStartsAt, TokenKindAbsentAt, TokenAt, before, tokens, token]

theorem independent_core_rejection : coreRejects source 3 before failed failure.toDiagnostic [] :=
  .selected .parenthesized selected
    (.firstRejected (span 0 1) ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
      (by simp [TokenKindAbsentAt, TokenAt, before, tokens, token]) ⟨rfl, rfl, rfl⟩)

private theorem rewind_continues : ¬ ExpressionAtomBoundaryStops (expressionAtomTraceRewind before failed) := by
  intro stops
  cases stops <;> simp_all [TokenAt, expressionAtomTraceRewind, before, failed, tokens, token]

private theorem plus_continues :
    ¬ ExpressionAtomRecoveryStops { before with cursor := 1, endIndex := 4 } { before with cursor := 1, endIndex := 4 } := by
  intro stops
  cases stops <;> simp_all [TokenAt, before, tokens, token]

private theorem independent_recovery : ExpressionAtomRecoveryTraceParses source 3
    (expressionAtomTraceRewind before failed) errorValue after [recoveryEvent] := by
  refine ⟨.recovered (token := token 0 1 .leftParen) ⟨by change 0 < 4; decide, rfl⟩
    (.next (token := token 1 2 .plus) plus_continues ⟨by change 1 < 4; decide, rfl⟩
      (.stop (.semicolon ⟨by change 2 < 4; decide, rfl⟩))), rfl⟩

theorem independent_public_recovery : ExpressionAtomTraceParses coreParses coreRejects source 3
    before errorValue after [failure.toDiagnostic, recoveryEvent] :=
  .recovered independent_core_rejection rewind_continues independent_recovery

/-- Reverse correspondence, not only direct evaluation, reconstructs the
changed numeric window and every incoming diagnostic exactly. -/
theorem public_reply_from_independent_trace (text : String) (prior : List ParseDiagnostic) :
    expressionAtom nested block (input text prior) = .ok errorValue (recovered text prior) :=
  (expressionAtom_trace_success_state_iff core_success_sound core_reject_sound core_success_complete
    core_reject_complete core_success_frame core_reject_frame (input := input text prior)).mp independent_public_recovery

theorem public_recovery_retains_failed_numeric_window (text : String) (prior : List ParseDiagnostic) :
    (recovered text prior).file = (input text prior).file ∧
    (recovered text prior).tokens = (input text prior).tokens ∧
    (recovered text prior).window.endByte = (input text prior).window.endByte ∧
    (recovered text prior).cursor = 2 ∧ (recovered text prior).window.endIndex = 4 ∧
    (recovered text prior).diagnostics = prior ++ [failure.toDiagnostic, recoveryEvent] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [recovered, State.diagnostics, List.reverse_cons, List.reverse_reverse, List.append_assoc]
  rfl

theorem prior_reports_are_preserved_with_multiplicity (text : String) (prior : List ParseDiagnostic) :
    expressionAtom nested block (input text (prior ++ [failure.toDiagnostic])) =
      .ok errorValue (recovered text (prior ++ [failure.toDiagnostic])) ∧
    (recovered text (prior ++ [failure.toDiagnostic])).diagnostics =
      prior ++ [failure.toDiagnostic, failure.toDiagnostic, recoveryEvent] :=
  ⟨public_reply_from_independent_trace text _, by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      (public_recovery_retains_failed_numeric_window text (prior ++ [failure.toDiagnostic])).2.2.2.2.2⟩

/-- Success-frame fields in the child contract are vacuous for always-rejecting
children; public recovery turns the unconstrained rejected endIndex into success. -/
theorem public_atom_has_no_unrestricted_fuel_contract (fuel : Nat) :
    ¬ UnrestrictedFuelElementContract (expressionAtom nested block) fuel := by
  intro contract
  have impossible := contract.endIndexOnSuccess (public_reply_from_independent_trace "" [])
  change 4 = 3 at impossible
  contradiction

theorem public_atom_has_no_full_window_success_context :
    ¬ ParserSuccessContext (expressionAtom nested block) := by
  intro contextFrame
  have impossible := congrArg TokenWindow.endIndex (contextFrame (public_reply_from_independent_trace "" [])).2
  change 4 = 3 at impossible
  contradiction

end Solcore.Test.SyntaxExpressionAtomNumericWindowProperties
