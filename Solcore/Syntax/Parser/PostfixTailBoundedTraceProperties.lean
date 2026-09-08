import Solcore.Syntax.Parser.PostfixTailTraceCorrespondenceProperties
import Solcore.Syntax.Parser.PostfixTailUnrestrictedFuelTotalityProperties

/-! Explicit loop and child budgets discharge pointwise invariant exclusion.
Completeness uses independent uniqueness/disjointness; non-vacuous outcome
existence instead uses ordinary execution and soundness alone. These claims
hold on arbitrary numerical States, not only valid token carriers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar

variable {nested : Parser Expr}
  {nestedTrace : SourceId → Nat → Remainder → Expr → Remainder → List ParseDiagnostic → Prop}
  {nestedRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}

variable (successSound : ParserTraceSuccessSound nested nestedTrace)
  (rejectSound : ParserTraceRejectSound nested nestedRejects)
  (contextFrame : ParserSuccessContext nested) (block : Parser Block)
  (nestedFuel loopFuel : Nat) (contract : UnrestrictedFuelElementContract nested nestedFuel)
  (base : Expr) {input : State} (loopAdequate : input.remainingCount < loopFuel)
  (nestedAdequate : input.remainingCount < nestedFuel + 1)

include successSound rejectSound contextFrame contract loopAdequate nestedAdequate
include block

theorem postfixTail_trace_success_complete_of_unrestrictedElementFuel
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    {value : Expr} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
      input.declarativeRemainder base value after trace) :
    ∃ output, postfixTail nested block loopFuel base input = .ok value output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace :=
  postfixTail_trace_success_complete_of_ne_invariant successSound rejectSound contextFrame
    block loopFuel base outcomes
    (postfixTail_ne_invariant_of_unrestrictedElementFuel nested block nestedFuel loopFuel
      contract base input loopAdequate nestedAdequate) parsed

theorem postfixTail_trace_reject_complete_of_unrestrictedElementFuel
    (outcomes : TraceExactOutcomeSpec nestedTrace nestedRejects input.file.id input.window.endByte)
    {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
      input.declarativeRemainder base after report trace) :
    ∃ failure rejected, postfixTail nested block loopFuel base input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace :=
  postfixTail_trace_reject_complete_of_ne_invariant successSound rejectSound contextFrame
    block loopFuel base outcomes
    (postfixTail_ne_invariant_of_unrestrictedElementFuel nested block nestedFuel loopFuel
      contract base input loopAdequate nestedAdequate) rejection

/-- Unlike joint exactness, this supplies an actual traced outcome. -/
theorem postfixTail_exists_trace_outcome_of_unrestrictedElementFuel :
    (∃ value output trace,
      postfixTail nested block loopFuel base input = .ok value output ∧
      PostfixTailTraceParses nestedTrace input.file.id input.window.endByte
        input.declarativeRemainder base value output.declarativeRemainder trace ∧
      output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      postfixTail nested block loopFuel base input = .reject failure rejected ∧
      PostfixTailTraceRejects nestedTrace nestedRejects input.file.id input.window.endByte
        input.declarativeRemainder base rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases postfixTail_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract
      loopFuel base input loopAdequate nestedAdequate with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases postfixTail_trace_success_sound successSound contextFrame block loopFuel base _ _ _ result with
      ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases postfixTail_reject_trace_sound successSound rejectSound contextFrame block loopFuel base _ _ _ result with
      ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

omit loopAdequate nestedAdequate in
theorem postfixTailTrace_outcome_exists_of_unrestrictedElementFuel
    (source : SourceId) (endByte : Nat) (input : Remainder)
    (adequate : input.endIndex - input.cursor < nestedFuel + 1) :
    (∃ value output trace, PostfixTailTraceParses nestedTrace source endByte input base value output trace) ∨
    (∃ rejected report trace, PostfixTailTraceRejects nestedTrace nestedRejects
      source endByte input base rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }, tokens := input.tokens, cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }, diagnosticsRev := []
  }
  rcases postfixTail_exists_trace_outcome_of_unrestrictedElementFuel successSound rejectSound contextFrame
      block nestedFuel (state.remainingCount + 1) contract base (Nat.lt_succ_self _) adequate with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, rejection⟩

end Solcore.Syntax.Parser.ExpressionAtomInternals
