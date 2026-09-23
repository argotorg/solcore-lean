import Solcore.Syntax.Parser.DiagnosticTraceCompletenessFromSoundnessProperties
import Solcore.Syntax.Parser.ExpressionNameRejectionTraceProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! The real Boolean-first checked-name leaf consumes all four generic APIs.
Earlier diagnostics are arbitrary, including malformed spans. Countermodels
separate independent exactness, vacuous completeness, and actual existence. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTraceCompletenessFromSoundnessProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem name_sound : ParserTraceSuccessSound expressionName ExpressionNameTraceParses :=
  expressionName_success_trace_sound

private theorem name_reject_sound : ParserTraceRejectSound expressionName ExpressionNameTraceRejects := by
  intro input rejected failure result
  have reflected := expressionName_reject_trace_sound result
  exact ⟨[], reflected.1, by rw [reflected.2]; simp only [List.append_nil]⟩

private theorem name_joint (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec ExpressionNameTraceParses ExpressionNameTraceRejects source endByte where
  successResultUnique := ExpressionNameTraceParses.result_unique
  rejectResultUnique := ExpressionNameTraceRejects.result_unique
  successRejectDisjoint := by
    rintro _ _ _ _ rejected ⟨_, _, _, parsed⟩
    exact rejected.disjoint_success parsed

theorem checked_name_success_from_soundness
    {input : State} (prior : List ParseDiagnostic) {name : Identifier} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : ExpressionNameTraceParses input.file.id input.window.endByte input.declarativeRemainder name after trace) :
    ∃ output, expressionName { input with diagnosticsRev := prior.reverse } = .ok name output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = prior ++ trace := by
  have result := trace_success_exists_ok_of_sound name_sound name_reject_sound
    (input := { input with diagnosticsRev := prior.reverse })
    (name_joint input.file.id input.window.endByte)
    (expressionName_ne_invariant _) parsed
  simpa only [State.diagnostics, List.reverse_reverse] using result

theorem checked_name_rejection_from_soundness
    {input : State} (prior : List ParseDiagnostic) {after : Remainder} {report : ParseDiagnostic}
    {trace : List ParseDiagnostic}
    (rejection : ExpressionNameTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace) :
    ∃ failure output, expressionName { input with diagnosticsRev := prior.reverse } = .reject failure output ∧
      output.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧ output.diagnostics = prior ++ trace := by
  have result := trace_reject_exists_reject_of_sound name_sound name_reject_sound
    (input := { input with diagnosticsRev := prior.reverse })
    (name_joint input.file.id input.window.endByte)
    (expressionName_ne_invariant _) rejection
  simpa only [State.diagnostics, List.reverse_reverse] using result

theorem checked_name_success_contract_from_soundness :
    ParserTraceSuccessComplete expressionName ExpressionNameTraceParses :=
  trace_success_complete_of_sound name_sound name_reject_sound name_joint expressionName_ne_invariant

theorem checked_name_rejection_contract_from_soundness :
    ParserTraceRejectComplete expressionName ExpressionNameTraceRejects :=
  trace_reject_complete_of_sound name_sound name_reject_sound name_joint expressionName_ne_invariant

private theorem identifier_has_no_boolean {input : State} {name : Identifier}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span := name.span, value := .identifier name.value }) :
    BooleanPatternAbsentAt input.declarativeRemainder := by
  constructor <;> rintro ⟨span, other⟩
  all_goals have impossible := congrArg (·.value) (present.token_unique other)
  all_goals cases impossible

theorem hyphen_event_follows_every_prior
    {input : State} (prior : List ParseDiagnostic) {name : Identifier}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span := name.span, value := .identifier name.value })
    (hyphen : IdentifierHyphenSpelling name.value) :
    ∃ output, expressionName { input with diagnosticsRev := prior.reverse } = .ok name output ∧
      output = { input with
        cursor := input.cursor + 1
        diagnosticsRev := { span := name.span, kind := .invalidIdentifierHyphen name.value } :: prior.reverse } ∧
      output.diagnostics = prior ++ [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] := by
  have parsed : ExpressionNameTraceParses input.file.id input.window.endByte input.declarativeRemainder name
      { input.declarativeRemainder with cursor := input.cursor + 1 }
      [{ span := name.span, kind := .invalidIdentifierHyphen name.value }] :=
    .identifier (identifier_has_no_boolean present) (.parsed ⟨present, rfl, rfl, rfl⟩ (.hyphen hyphen))
  rcases checked_name_success_from_soundness prior parsed with ⟨output, result, _, events⟩
  exact ⟨output, result, expressionName_success_state_eq_of_trace result parsed, events⟩

private def plusFailure (span : SourceSpan) : Failure := {
  span, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .expression
}

theorem plus_rejection_never_commits_report
    {input : State} (prior : List ParseDiagnostic) {span : SourceSpan}
    (present : TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .plus }) :
    expressionName { input with diagnosticsRev := prior.reverse } =
      .reject (plusFailure span) { input with diagnosticsRev := prior.reverse } ∧
    ({ input with diagnosticsRev := prior.reverse } : State).diagnostics = prior := by
  have absent : BooleanPatternAbsentAt input.declarativeRemainder := by
    constructor <;> rintro ⟨otherSpan, other⟩
    all_goals have impossible := congrArg (·.value) (present.token_unique other)
    all_goals cases impossible
  have noName : IdentifierAbsentAt input.declarativeRemainder := by
    rintro ⟨otherSpan, text, other⟩
    have impossible := congrArg (·.value) (present.token_unique other)
    cases impossible
  have rejection : ExpressionNameTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      input.declarativeRemainder (plusFailure span).toDiagnostic [] :=
    ⟨absent, .absent noName,
      .reported (CurrentInputAt.token (source := input.file.id) (endByte := input.window.endByte)
        (input := input.declarativeRemainder) present), rfl⟩
  rcases checked_name_rejection_from_soundness prior rejection with ⟨failure, output, result, _, reportEq, events⟩
  have stateEq := (expressionName_reject_trace_sound result).2
  cases Failure.toDiagnostic_injective reportEq
  exact ⟨stateEq ▸ result, by simpa only [stateEq, List.append_nil] using events⟩

private def stops (input : State) : Reply Unit :=
  .invariant (.fuelExhausted .typeExpr input.currentSpan)

private def phantom (_source : SourceId) (_endByte : Nat) (input : Remainder)
    (_value : Unit) (output : Remainder) (trace : List ParseDiagnostic) : Prop :=
  output = input ∧ trace = []

private def emptySuccess (_source : SourceId) (_endByte : Nat) (_input : Remainder)
    (_value : Unit) (_output : Remainder) (_trace : List ParseDiagnostic) : Prop := False

private def emptyRejection (_source : SourceId) (_endByte : Nat) (_input _output : Remainder)
    (_report : ParseDiagnostic) (_trace : List ParseDiagnostic) : Prop := False

private theorem phantom_joint (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec phantom emptyRejection source endByte where
  successResultUnique := by
    rintro input ⟨⟩ ⟨⟩ _ _ _ _ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  rejectResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
  successRejectDisjoint := by intro _ _ _ _ impossible; exact False.elim impossible

/-- Both soundness contracts and a nonempty exact success grammar can coexist
with invariant-only execution. The explicit exclusion premise cannot be dropped. -/
theorem sound_joint_does_not_replace_invariant_exclusion (input : State) :
    TraceExactOutcomeSpec phantom emptyRejection input.file.id input.window.endByte ∧
    ParserTraceSuccessSound stops phantom ∧ ParserTraceRejectSound stops emptyRejection ∧
    phantom input.file.id input.window.endByte input.declarativeRemainder () input.declarativeRemainder [] ∧
    (¬ ∃ output, stops input = .ok () output) ∧
    (¬ ∀ error, stops input ≠ .invariant error) := by
  refine ⟨phantom_joint _ _, ?_, ?_, ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro _ _ _ impossible; cases impossible
  · intro _ _ _ impossible; cases impossible
  · rintro ⟨_, impossible⟩; cases impossible
  · intro excluded
    exact excluded (.fuelExhausted .typeExpr input.currentSpan) rfl

/-- Empty grammars have vacuous completeness even when the parser never gives
an ordinary reply. These contracts do not assert outcome existence. -/
theorem empty_completeness_does_not_assert_existence (input : State) :
    TraceExactOutcomeSpec emptySuccess emptyRejection input.file.id input.window.endByte ∧
    ParserTraceSuccessComplete stops emptySuccess ∧ ParserTraceRejectComplete stops emptyRejection ∧
    (¬ ((∃ value output, stops input = .ok value output) ∨
      ∃ failure output, stops input = .reject failure output)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact {
      successResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      rejectResultUnique := by intro _ _ _ _ _ _ _ impossible; exact False.elim impossible
      successRejectDisjoint := by intro _ _ _ _ impossible; exact False.elim impossible
    }
  · intro _ _ _ _ impossible; exact False.elim impossible
  · intro _ _ _ _ impossible; exact False.elim impossible
  · rintro (⟨_, _, impossible⟩ | ⟨_, _, impossible⟩) <;> cases impossible

end Solcore.Test.SyntaxTraceCompletenessFromSoundnessProperties
