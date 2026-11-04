import Solcore.Syntax.Parser.Internal.LambdaParameterRecovery
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Internal.ParameterTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.CoreLambdaParameterRecoveryOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PrimitiveRejectionDiagnosticProperties
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Parser.FunctionParameterBoundaryOutcomeSoundnessProperties

/-!
Parser side of the parameter traces: raw and core parameters, tails,
recovery and dispatch.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterDispatchTraceProperties

/-! Shared exact lookahead for non-recovering function and lambda parameters.
The contextual marker is selected only when the next identifier is visible in
the active window. These proof-side projections do not execute either branch
and do not alter the parser, state, or diagnostic history. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

namespace ParameterDispatchTraceInternals

def comptimeGuard (input : State) : Bool :=
  isContextual input .comptime &&
    match input.peekOffsetKind? 1 with
    | some (.identifier _) => true
    | _ => false

theorem comptimeGuard_true_iff {input : State} :
    comptimeGuard input = true ↔ ComptimeLambdaParameterStartsAt input.declarativeRemainder := by
  constructor
  · intro guard
    rcases Bool.and_eq_true_iff.mp guard with ⟨markerPresent, namePresent⟩
    rcases contextual_eq_ok_of_isContextual_eq_true .comptime .parameter markerPresent with
      ⟨marker, markerResult⟩
    have advanced : isIdentifier { input with cursor := input.cursor + 1 } = true := namePresent
    rcases identifierPresentAt_of_isIdentifier_eq_true advanced with ⟨nameSpan, spelling, nameToken⟩
    exact ⟨marker.span, nameSpan, spelling,
      (contextual_success_exactTokenParses .comptime .parameter markerResult).1, nameToken⟩
  · rintro ⟨markerSpan, nameSpan, spelling, markerToken, nameToken⟩
    change TokenAt input.tokens input.window.endIndex input.cursor
      { span := markerSpan, value := .identifier ContextualKeyword.comptime.spelling } at markerToken
    change TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := nameSpan, value := .identifier spelling } at nameToken
    have markerPresent : isContextual input .comptime = true := by
      unfold isContextual State.peekKind? State.peek?
      simp only [markerToken.1, if_true, markerToken.2, Option.map_some, TokenKind.isContextual]
      exact beq_iff_eq.mpr rfl
    have namePresent : (match input.peekOffsetKind? 1 with
        | some (.identifier _) => true | _ => false) = true := by
      simp only [State.peekOffsetKind?, State.peekOffset?, nameToken.1, if_true,
        nameToken.2, Option.map_some]
    exact Bool.and_eq_true_iff.mpr ⟨markerPresent, namePresent⟩

theorem comptimeGuard_false_iff {input : State} :
    comptimeGuard input = false ↔ ComptimeParameterPrefixAbsentAt input.declarativeRemainder := by
  change comptimeGuard input = false ↔ ¬ ComptimeLambdaParameterStartsAt input.declarativeRemainder
  rw [← comptimeGuard_true_iff]
  exact Bool.eq_false_iff

theorem comptimeGuard_eq_of_remainder_eq {left right : State}
    (same : left.declarativeRemainder = right.declarativeRemainder) :
    comptimeGuard left = comptimeGuard right := by
  have equivalent : comptimeGuard left = true ↔ comptimeGuard right = true := by
    rw [comptimeGuard_true_iff, comptimeGuard_true_iff, same]
  cases leftValue : comptimeGuard left <;> cases rightValue : comptimeGuard right <;> simp_all

end ParameterDispatchTraceInternals

theorem FunctionParameterInternals.namedParameterCore_eq_comptime_of_prefix
    {input : State} (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder) :
    FunctionParameterInternals.namedParameterCore input =
      FunctionParameterInternals.comptimeNamedParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_true_iff.mpr present]
  rfl

theorem FunctionParameterInternals.namedParameterCore_eq_ordinary_of_prefix_absent
    {input : State} (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder) :
    FunctionParameterInternals.namedParameterCore input =
      FunctionParameterInternals.ordinaryNamedParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_false_iff.mpr absent]
  rfl

theorem LambdaParameterInternals.lambdaParameterCore_eq_comptime_of_prefix
    {input : State} (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder) :
    LambdaParameterInternals.lambdaParameterCore input =
      LambdaParameterInternals.comptimeLambdaParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_true_iff.mpr present]
  rfl

theorem LambdaParameterInternals.lambdaParameterCore_eq_ordinary_of_prefix_absent
    {input : State} (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder) :
    LambdaParameterInternals.lambdaParameterCore input =
      LambdaParameterInternals.ordinaryLambdaParameter input := by
  change (if ParameterDispatchTraceInternals.comptimeGuard input then _ else _) = _
  rw [ParameterDispatchTraceInternals.comptimeGuard_false_iff.mpr absent]
  rfl

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterNameFinishingTraceProperties

/-! Exact state bridges for the inline ordinary-name check shared by named
and lambda parameters. No executable helper is introduced. A continuation law
retains every result, including the complete Failure and State on rejection.
The checked prefix is not the pair-selected parameter core or public recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem parameterNameFinishing_eq_ok_of_trace (name : Identifier) (input : State)
    {trace : List ParseDiagnostic} (events : ParameterNameFinishingTrace name trace) :
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
    else pure ()) input = .ok () { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary spelling => simp only [beq_eq_false_iff_ne.mpr spelling, Bool.false_eq_true, if_false]; rfl
  | comptime spelling => simp only [spelling, beq_self_eq_true, if_true]; rfl

theorem parameterNameFinishing_success_trace_sound (name : Identifier)
    {input output : State} {value : Unit}
    (result : (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
      else pure ()) input = .ok value output) :
    ∃ trace, ParameterNameFinishingTrace name trace ∧ value = () ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases parameterNameFinishingTrace_exists name with ⟨trace, events⟩
  have expected := parameterNameFinishing_eq_ok_of_trace name input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem parameterNameFinishing_trace_success_state_iff (name : Identifier) (input : State)
    {trace : List ParseDiagnostic} :
    ParameterNameFinishingTrace name trace ↔
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName }
    else pure ()) input = .ok () { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  constructor
  · exact parameterNameFinishing_eq_ok_of_trace name input
  · intro result
    rcases parameterNameFinishing_success_trace_sound name result with ⟨actual, events, _, stateEq⟩
    have reversed := congrArg State.diagnosticsRev stateEq
    have same := List.append_cancel_right reversed
    have sameTrace := congrArg List.reverse same
    simp only [List.reverse_reverse] at sameTrace
    exact sameTrace ▸ events

/-- The original inline conditional can be followed by any parser. The check
changes only the reverse event accumulator and never commits a Failure. -/
theorem parameterNameFinishing_continue_of_trace {α : Type} (name : Identifier)
    (next : Parser α) (input : State) {trace : List ParseDiagnostic}
    (events : ParameterNameFinishingTrace name trace) :
    (if name.value == ContextualKeyword.comptime.spelling then
      emitDiagnostic { span := name.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>= fun _ => next
    else next) input = next { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary spelling => simp only [beq_eq_false_iff_ne.mpr spelling, Bool.false_eq_true, if_false]; rfl
  | comptime spelling => simp only [spelling, beq_self_eq_true, if_true]; rfl

/-- Combine the real checked identifier with the subsequent inline spelling
check. Identifier events precede finishing events for every incoming State;
the continuation result itself is neither inspected nor weakened. -/
theorem checkedParameterName_continue_of_trace {α : Type} (next : Identifier → Parser α)
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    (identifier .parameter >>= fun found =>
      if found.value == ContextualKeyword.comptime.spelling then
        emitDiagnostic { span := found.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>=
          fun _ => next found
      else next found) input = next name (input.traceResult after trace) := by
  cases parsed with
  | parsed identifierTrace finishingTrace =>
      rcases (identifier_trace_success_iff .parameter).mp identifierTrace with
        ⟨afterName, nameResult, remainderEq, nameEvents⟩
      have window := identifier_preservesTokenWindow .parameter input
      rw [nameResult] at window
      have nameState := State.eq_traceResult_of_fields
        ((identifier_preservesFile .parameter).file_eq_of_ok nameResult)
        (congrArg TokenWindow.endByte window.2) remainderEq nameEvents
      have finished := parameterNameFinishing_continue_of_trace name (next name) afterName finishingTrace
      simp only [bind] at finished
      simp only [bind, nameResult]
      rw [finished, nameState]
      simp only [State.traceResult, List.reverse_append, List.append_assoc]

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterRecoveryTraceStateProperties

/-! Standalone recovery appends exactly one event on success, retains the
complete source/window, and rejects without committing its terminal report.
The scan never replays diagnostics from the tokens that it skips. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

private theorem advance_state {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      rfl

theorem recoverParameterAux_success_frame (first : SourceSpan) :
    ∀ fuel last {input output : State} {value : FunctionParameter},
      recoverParameterAux first last fuel input = .ok value output →
      output.file = input.file ∧
        output.diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  intro fuel
  induction fuel with
  | zero => intro last input output value result; simp [recoverParameterAux] at result
  | succ fuel ih =>
      intro last input output value result
      unfold recoverParameterAux at result
      split at result
      · unfold finishRecoveredParameter at result
        cases result
        exact ⟨rfl, by simp [State.emit, State.diagnostics, parameterRecoveryTraceEvent]⟩
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredParameter at result
            cases result
            exact ⟨rfl, by simp [State.emit, State.diagnostics, parameterRecoveryTraceEvent]⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            have shape := advance_state advanced
            subst next
            exact ih token.span (input := { input with cursor := input.cursor + 1 }) result

theorem recoverParameter_success_frame {input output : State} {value : FunctionParameter}
    (result : recoverParameter input = .ok value output) :
    output.file = input.file ∧ output.diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none => simp [advanced, rejectAt] at result
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      have frame := recoverParameterAux_success_frame token.span (next.remainingCount + 1) token.span result
      rw [advance_state advanced] at frame
      exact frame

theorem recoverParameter_reject_shape {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    rejected = input ∧ (rejectAt input { head := .identifier, tail := [] } .parameter : Reply FunctionParameter) =
      .reject failure input := by
  unfold recoverParameter at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact ⟨rfl, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverParameterAux_production_exists_ok token.span token.span next with ⟨value, output, success⟩
      rw [success] at result
      contradiction

theorem recoverParameter_preservesFile : Parser.PreservesFile recoverParameter := by
  intro input
  cases result : recoverParameter input with
  | invariant error => trivial
  | ok value output => exact (recoverParameter_success_frame result).1
  | reject failure rejected => rw [(recoverParameter_reject_shape result).1]; rfl

theorem recoverParameter_success_context : ParserSuccessContext recoverParameter := by
  intro input output value result
  have window := recoverParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨(recoverParameter_success_frame result).1, window.2⟩

theorem recoverParameter_reject_context {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [(recoverParameter_reject_shape result).1]
  exact ⟨rfl, rfl⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterRecoveryTraceProperties

/-! Standalone recovery has unrestricted exact trace contracts. Completeness
uses ordinary execution, not existence from the independent joint specification.
The caller's earlier failure report is neither reconstructed nor re-emitted. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem recoverParameter_trace_success_sound :
    ParserTraceSuccessSound recoverParameter FunctionParameterRecoveryTraceParses := by
  intro input output value result
  exact ⟨[parameterRecoveryTraceEvent value.span],
    ⟨recoverParameter_success_ordinary_sound result, rfl⟩, (recoverParameter_success_frame result).2⟩

theorem recoverParameter_reject_trace_sound :
    ParserTraceRejectSound recoverParameter FunctionParameterRecoveryTraceRejects := by
  intro input rejected failure result
  have ordinary := recoverParameter_reject_ordinary_sound result
  rcases recoverParameter_reject_shape result with ⟨rfl, reported⟩
  exact ⟨[], ⟨ordinary, (rejectAt_reject_reports _ .parameter reported).1, rfl⟩, by simp⟩

theorem recoverParameter_trace_success_complete :
    ParserTraceSuccessComplete recoverParameter FunctionParameterRecoveryTraceParses :=
  trace_success_complete_of_sound recoverParameter_trace_success_sound recoverParameter_reject_trace_sound
    (fun _ _ => functionParameterRecoveryTraceExactOutcomeSpec) recoverParameter_ne_invariant

theorem recoverParameter_trace_reject_complete :
    ParserTraceRejectComplete recoverParameter FunctionParameterRecoveryTraceRejects :=
  trace_reject_complete_of_sound recoverParameter_trace_success_sound recoverParameter_reject_trace_sound
    (fun _ _ => functionParameterRecoveryTraceExactOutcomeSpec) recoverParameter_ne_invariant

theorem recoverParameter_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, recoverParameter input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverParameter_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases recoverParameter_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem recoverParameter_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, recoverParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact recoverParameter_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases recoverParameter_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem recoverParameter_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, recoverParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [recoverParameter_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem recoverParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases recoverParameter_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := recoverParameter_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverParameter_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := recoverParameter_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact recoverParameter_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverParameter_trace_reject_failure_state_iff.mpr result

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties

/-! Lambda recovery retags only the recovered error AST. Exact function
recovery supplies its whole state, events, complete Failure, and unconditional
ordinary outcome. No caller report is committed or re-emitted by this wrapper. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem recoverLambdaParameter_trace_success_sound :
    ParserTraceSuccessSound recoverLambdaParameter LambdaParameterRecoveryTraceParses := by
  intro input output value result
  unfold recoverLambdaParameter at result
  cases recovered : recoverParameter input with
  | invariant error => simp [recovered] at result
  | reject failure rejected => simp [recovered] at result
  | ok parameter next =>
      simp only [recovered] at result
      cases result
      rcases recoverParameter_trace_success_sound recovered with ⟨trace, parsed, events⟩
      exact ⟨trace, .recovered parsed, events⟩

theorem recoverLambdaParameter_reject_trace_sound :
    ParserTraceRejectSound recoverLambdaParameter LambdaParameterRecoveryTraceRejects := by
  intro input rejected failure result
  unfold recoverLambdaParameter at result
  cases recovered : recoverParameter input with
  | invariant error => simp [recovered] at result
  | ok parameter next => simp [recovered] at result
  | reject actual next =>
      simp only [recovered] at result
      cases result
      exact recoverParameter_reject_trace_sound recovered

theorem recoverLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      recoverLambdaParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | recovered recovery =>
        simp only [recoverLambdaParameter, recoverParameter_trace_success_state_iff.mp recovery]
  · intro result
    rcases recoverLambdaParameter_trace_success_sound result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem recoverLambdaParameter_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      recoverLambdaParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [recoverLambdaParameter, recoverParameter_trace_reject_failure_state_iff.mp rejection]
  · intro result
    rcases recoverLambdaParameter_reject_trace_sound result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem recoverLambdaParameter_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, recoverLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases recoverParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, recoverLambdaParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ recoverLambdaParameter_trace_reject_failure_state_iff.mpr result

theorem recoverLambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete recoverLambdaParameter LambdaParameterRecoveryTraceParses := by
  intro input value after trace parsed
  exact ⟨_, recoverLambdaParameter_trace_success_state_iff.mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem recoverLambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete recoverLambdaParameter LambdaParameterRecoveryTraceRejects := by
  intro input after report trace rejection
  rcases recoverLambdaParameter_trace_reject_state_iff.mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem recoverLambdaParameter_preservesFile : Parser.PreservesFile recoverLambdaParameter := by
  intro input
  unfold recoverLambdaParameter
  cases result : recoverParameter input with
  | invariant error => trivial
  | ok parameter next => exact recoverParameter_preservesFile.file_eq_of_ok result
  | reject failure rejected => exact recoverParameter_preservesFile.file_eq_of_reject result

theorem recoverLambdaParameter_success_context : ParserSuccessContext recoverLambdaParameter := by
  intro input output value result
  have window := recoverLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨recoverLambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem recoverLambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : recoverLambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := recoverLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨recoverLambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.TypedParameterFinishingTraceProperties

/-! Exact execution of both parameter finishers on every state. The complete
AST and state are fixed; only the finishing events are appended. Previously
emitted type/name diagnostics remain prior events, never regenerated here. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem finishTypedParameter_eq_ok_of_trace (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input : State) {trace : List ParseDiagnostic}
    (events : TypedParameterFinishingTrace type trace) :
    finishTypedParameter start marker name type input =
      .ok (typedParameterTraceValue start marker name type)
        { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events with
  | ordinary allowed =>
      cases kind : type.value <;> simp only [ParameterTypeAllowed, kind] at allowed
      all_goals simp only [finishTypedParameter, kind, pure]; rfl
  | comptime forbidden =>
      cases kind : type.value <;> simp [ParameterTypeAllowed, kind] at forbidden
      simp only [finishTypedParameter, kind, emitDiagnostic, modifyState, bind, pure]
      rfl

theorem finishTypedParameter_success_trace_sound (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) {input output : State} {value : FunctionParameter}
    (result : finishTypedParameter start marker name type input = .ok value output) :
    ∃ trace, TypedParameterFinishingTrace type trace ∧ value = typedParameterTraceValue start marker name type ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  have expected := finishTypedParameter_eq_ok_of_trace start marker name type input events
  rw [result] at expected
  exact ⟨trace, events, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem finishTypedParameter_success_context (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) : ParserSuccessContext (finishTypedParameter start marker name type) := by
  intro input output value result
  rcases finishTypedParameter_success_trace_sound start marker name type result with ⟨_, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem finishTypedParameter_trace_success_iff (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) {input : State} {trace : List ParseDiagnostic} :
    TypedParameterFinishingTrace type trace ↔
      ∃ output, finishTypedParameter start marker name type input =
        .ok (typedParameterTraceValue start marker name type) output ∧
        output.declarativeRemainder = input.declarativeRemainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, finishTypedParameter_eq_ok_of_trace start marker name type input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases finishTypedParameter_success_trace_sound start marker name type result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem finishTypedParameter_ne_reject (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input rejected : State) (failure : Failure) :
    finishTypedParameter start marker name type input ≠ .reject failure rejected := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  intro impossible
  contradiction

theorem finishTypedParameter_ne_invariant (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) (input : State) (error : ParserInvariantError) :
    finishTypedParameter start marker name type input ≠ .invariant error := by
  rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  intro impossible
  contradiction

theorem errorParameter_eq_ok_of_trace (span : SourceSpan) (constraint : ParseConstraint)
    (input : State) {trace : List ParseDiagnostic} (events : ErrorParameterFinishingTrace span constraint trace) :
    errorParameter span constraint input = .ok (errorParameterTraceValue span)
      { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  cases events
  rfl

theorem errorParameter_success_trace_sound (span : SourceSpan) (constraint : ParseConstraint)
    {input output : State} {value : FunctionParameter} (result : errorParameter span constraint input = .ok value output) :
    ∃ trace, ErrorParameterFinishingTrace span constraint trace ∧ value = errorParameterTraceValue span ∧
      output = { input with diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have expected := errorParameter_eq_ok_of_trace span constraint input .emitted
  rw [result] at expected
  exact ⟨_, .emitted, (Reply.ok.inj expected).1, (Reply.ok.inj expected).2⟩

theorem errorParameter_success_context (span : SourceSpan) (constraint : ParseConstraint) :
    ParserSuccessContext (errorParameter span constraint) := by
  intro input output value result
  rcases errorParameter_success_trace_sound span constraint result with ⟨_, _, _, same⟩
  rw [same]
  exact ⟨rfl, rfl⟩

theorem errorParameter_trace_success_iff (span : SourceSpan) (constraint : ParseConstraint)
    {input : State} {trace : List ParseDiagnostic} :
    ErrorParameterFinishingTrace span constraint trace ↔
      ∃ output, errorParameter span constraint input = .ok (errorParameterTraceValue span) output ∧
        output.declarativeRemainder = input.declarativeRemainder ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro events
    refine ⟨_, errorParameter_eq_ok_of_trace span constraint input events, rfl, ?_⟩
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  · rintro ⟨output, result, _, diagnostics⟩
    rcases errorParameter_success_trace_sound span constraint result with ⟨actual, events, _, same⟩
    rw [same] at diagnostics
    simp only [State.diagnostics, List.reverse_append, List.reverse_reverse] at diagnostics
    have traceEq := List.append_cancel_left diagnostics
    simpa only [traceEq] using events

theorem errorParameter_ne_reject (span : SourceSpan) (constraint : ParseConstraint)
    (input rejected : State) (failure : Failure) : errorParameter span constraint input ≠ .reject failure rejected := by
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  intro impossible
  contradiction

theorem errorParameter_ne_invariant (span : SourceSpan) (constraint : ParseConstraint)
    (input : State) (error : ParserInvariantError) : errorParameter span constraint input ≠ .invariant error := by
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  intro impossible
  contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterTailTraceProperties

/-! Exact raw named-parameter tail execution on arbitrary states. The colon is
silent; successful type events precede finishing events. Missing colons recover
with an error parameter, whereas type rejection forwards its uncommitted report. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

variable (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
  (errorSpan : SourceSpan)

theorem namedParameterTail_eq_of_absent {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    namedParameterTail start marker name errorSpan input =
      errorParameter errorSpan .namedParameterRequiresType input := by
  simp only [namedParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false]

theorem namedParameterTail_eq_of_present {input : State} {span : SourceSpan}
    (colon : TokenAt input.tokens input.window.endIndex input.cursor
      { span, value := .symbol .colon }) :
    namedParameterTail start marker name errorSpan input =
      match typeExpr { input with cursor := input.cursor + 1 } with
      | .ok type next => finishTypedParameter start marker name type next
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  have parsed : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨colon, rfl⟩
  simp only [namedParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon parsed, if_true,
    symbol_eq_ok_of_exactTokenParses .colon .parameter parsed]
  cases typeExpr { input with cursor := input.cursor + 1 } <;> rfl

theorem namedParameterTail_eq_ok_of_trace {input : State} {value : FunctionParameter}
    {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : NamedParameterTailTraceParses start marker name errorSpan input.file.id
      input.window.endByte input.declarativeRemainder value after trace) :
    namedParameterTail start marker name errorSpan input =
      .ok value (input.traceResult after trace) := by
  cases parsed with
  | typed colonSpan colon typeParsed finished =>
      have equation := namedParameterTail_eq_of_present start marker name errorSpan colon.1
      rcases colon with ⟨_, rfl⟩
      have typeResult := typeExpr_trace_success_state_iff.mp
        (show TypeExprTraceParses _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from typeParsed)
      simp only [equation, typeResult,
        finishTypedParameter_eq_ok_of_trace start marker name _ _ finished,
        State.traceResult, List.reverse_append, List.append_assoc]
  | typeMissing absent finished =>
      rw [namedParameterTail_eq_of_absent start marker name errorSpan absent,
        errorParameter_eq_ok_of_trace errorSpan .namedParameterRequiresType input finished]
      rfl

theorem namedParameterTail_eq_reject_of_trace {input : State} {failure : Failure}
    {after : Remainder} {trace : List ParseDiagnostic}
    (rejection : NamedParameterTailTraceRejects start marker name errorSpan input.file.id
      input.window.endByte input.declarativeRemainder after failure.toDiagnostic trace) :
    namedParameterTail start marker name errorSpan input =
      .reject failure (input.traceResult after trace) := by
  cases rejection with
  | typeRejected colonSpan colon typeRejected =>
      have equation := namedParameterTail_eq_of_present start marker name errorSpan colon.1
      rcases colon with ⟨_, rfl⟩
      have typeResult := typeExpr_trace_reject_failure_state_iff.mp
        (show TypeExprTraceRejects _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from typeRejected)
      rw [equation, typeResult]
      rfl

theorem namedParameterTail_trace_success_sound :
    ParserTraceSuccessSound (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceParses start marker name errorSpan) := by
  intro input output value result
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject failure rejected => simp [typeResult] at result
    | ok type next =>
        simp only [typeResult] at result
        rcases typeExpr_trace_success_sound typeResult with ⟨typeEvents, parsed, events⟩
        rcases finishTypedParameter_success_trace_sound start marker name type result with
          ⟨finishEvents, finished, rfl, rfl⟩
        refine ⟨typeEvents ++ finishEvents,
          .typed colon.span (symbol_success_exactTokenParses .colon .parameter colonResult)
            parsed finished, ?_⟩
        simpa only [State.diagnostics, List.reverse_append, List.reverse_reverse,
          List.append_assoc] using congrArg (· ++ finishEvents) events
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent] at result
    rcases errorParameter_success_trace_sound errorSpan .namedParameterRequiresType result with
      ⟨trace, finished, rfl, rfl⟩
    exact ⟨trace, .typeMissing absent finished, by
      simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]⟩

theorem namedParameterTail_reject_trace_sound :
    ParserTraceRejectSound (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) := by
  intro input rejected failure result
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type next =>
        exact False.elim (finishTypedParameter_ne_reject start marker name type next rejected failure
          (by simpa only [typeResult] using result))
    | reject actual next =>
        simp only [typeResult] at result
        cases result
        rcases typeExpr_reject_trace_sound typeResult with ⟨trace, rejection, events⟩
        exact ⟨trace, .typeRejected colon.span
          (symbol_success_exactTokenParses .colon .parameter colonResult) rejection, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent] at result
    exact False.elim (errorParameter_ne_reject errorSpan .namedParameterRequiresType input rejected failure result)

theorem namedParameterTail_trace_success_complete :
    ParserTraceSuccessComplete (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceParses start marker name errorSpan) := by
  intro input value after trace parsed
  exact ⟨_, namedParameterTail_eq_ok_of_trace start marker name errorSpan parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_complete :
    ParserTraceRejectComplete (namedParameterTail start marker name errorSpan)
      (NamedParameterTailTraceRejects start marker name errorSpan) := by
  intro input after report trace rejection
  cases rejection with
  | typeRejected colonSpan colon rejected =>
      rcases colon with ⟨token, rfl⟩
      rcases typeExpr_trace_reject_state_iff.mp
        (show TypeExprTraceRejects _ _
          ({ input with cursor := input.cursor + 1 } : State).declarativeRemainder _ _ _ from rejected)
        with ⟨failure, result, reportEq⟩
      refine ⟨failure, input.traceResult after trace, ?_, rfl, reportEq,
        input.traceResult_diagnostics after trace⟩
      rw [namedParameterTail_eq_of_present start marker name errorSpan token, result]
      rfl

theorem namedParameterTail_ordinary : Parser.Ordinary (namedParameterTail start marker name errorSpan) := by
  intro input
  by_cases present : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter present with ⟨colon, colonResult⟩
    rw [namedParameterTail_eq_of_present start marker name errorSpan
      (symbol_ok_tokenAt .colon .parameter colonResult).1]
    rcases typeExpr_ordinary { input with cursor := input.cursor + 1 } with
      ⟨type, next, result⟩ | ⟨failure, rejected, result⟩
    · rw [result]
      rcases typedParameterFinishingTrace_exists type with ⟨trace, events⟩
      exact Or.inl ⟨_, _, finishTypedParameter_eq_ok_of_trace start marker name type next events⟩
    · exact Or.inr ⟨failure, rejected, by rw [result]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr present)
    rw [namedParameterTail_eq_of_absent start marker name errorSpan absent]
    exact Or.inl ⟨_, _, errorParameter_eq_ok_of_trace errorSpan .namedParameterRequiresType input .emitted⟩

theorem namedParameterTail_ne_invariant (input : State) (error : ParserInvariantError) :
    namedParameterTail start marker name errorSpan input ≠ .invariant error := by
  intro failed
  rcases namedParameterTail_ordinary start marker name errorSpan input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterTailTraceStateProperties

/-! Bidirectional tail correspondence fixes the AST, full Failure, every state
field, and the ordered diagnostic suffix. No validity or child contracts are
required. These laws concern the raw tail, not outer parameter recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

variable (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
  (errorSpan : SourceSpan)

theorem namedParameterTail_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceParses start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, namedParameterTail start marker name errorSpan input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterTail_trace_success_complete start marker name errorSpan
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameterTail_trace_success_sound start marker name errorSpan result with
      ⟨actualTrace, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameterTail_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameterTail start marker name errorSpan input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterTail_trace_reject_complete start marker name errorSpan
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameterTail_reject_trace_sound start marker name errorSpan result with
      ⟨actualTrace, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameterTail_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameterTail start marker name errorSpan input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, namedParameterTail_eq_reject_of_trace start marker name errorSpan rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact (namedParameterTail_trace_reject_iff start marker name errorSpan).mpr
      ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameterTail_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceParses start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      namedParameterTail start marker name errorSpan input = .ok value (input.traceResult after trace) := by
  constructor
  · exact namedParameterTail_eq_ok_of_trace start marker name errorSpan
  · intro result
    exact (namedParameterTail_trace_success_iff start marker name errorSpan).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      namedParameterTail start marker name errorSpan input = .reject failure (input.traceResult after trace) := by
  constructor
  · exact namedParameterTail_eq_reject_of_trace start marker name errorSpan
  · intro result
    exact (namedParameterTail_trace_reject_failure_iff start marker name errorSpan).mpr
      ⟨_, result, input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameterTail_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTailTraceRejects start marker name errorSpan input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameterTail start marker name errorSpan input =
        .reject failure (input.traceResult after trace) ∧ failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete start marker name errorSpan rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameterTail_eq_reject_of_trace start marker name errorSpan
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (namedParameterTail_trace_reject_failure_state_iff start marker name errorSpan).mpr result

theorem namedParameterTail_preservesFile :
    Parser.PreservesFile (namedParameterTail start marker name errorSpan) := by
  intro input
  cases result : namedParameterTail start marker name errorSpan input with
  | invariant error => trivial
  | ok value output =>
      rcases namedParameterTail_trace_success_sound start marker name errorSpan result with ⟨trace, parsed, _⟩
      have expected := namedParameterTail_eq_ok_of_trace start marker name errorSpan parsed
      rw [result] at expected
      rw [(Reply.ok.inj expected).2]
      rfl
  | reject failure rejected =>
      rcases namedParameterTail_reject_trace_sound start marker name errorSpan result with ⟨trace, rejection, _⟩
      have expected := namedParameterTail_eq_reject_of_trace start marker name errorSpan rejection
      rw [result] at expected
      rw [(Reply.reject.inj expected).2]
      rfl

theorem namedParameterTail_success_context :
    ParserSuccessContext (namedParameterTail start marker name errorSpan) := by
  intro input output value result
  have window := namedParameterTail_preservesTokenWindow start marker name errorSpan input
  rw [result] at window
  exact ⟨(namedParameterTail_preservesFile start marker name errorSpan).file_eq_of_ok result, window.2⟩

theorem namedParameterTail_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameterTail start marker name errorSpan input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameterTail_preservesTokenWindow start marker name errorSpan input
  rw [result] at window
  exact ⟨(namedParameterTail_preservesFile start marker name errorSpan).file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.ParameterSourceFrameProperties

/-! Every ordinary raw function/lambda parameter reply preserves the complete
input source file. Diagnostic-producing finishers and retagging do not alter
that source. Recovery loops and public recovering wrappers are not covered. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace FunctionParameterInternals

theorem finishTypedParameter_preservesFile (start : SourceSpan) (marker : Option SourceSpan)
    (name : Identifier) (type : TypeExpr) :
    Parser.PreservesFile (finishTypedParameter start marker name type) := by
  intro input
  rcases DeclarativeGrammar.typedParameterFinishingTrace_exists type with ⟨trace, events⟩
  rw [finishTypedParameter_eq_ok_of_trace start marker name type input events]
  rfl

theorem errorParameter_preservesFile (span : SourceSpan) (constraint : ParseConstraint) :
    Parser.PreservesFile (errorParameter span constraint) := by
  intro input
  rw [errorParameter_eq_ok_of_trace span constraint input .emitted]
  rfl

theorem ordinaryNamedParameter_preservesFile : Parser.PreservesFile ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact namedParameterTail_preservesFile name.span none name name.span
  · simp only [warned, Bool.false_eq_true, if_false]
    exact namedParameterTail_preservesFile name.span none name name.span

theorem comptimeNamedParameter_preservesFile : Parser.PreservesFile comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .parameter)
  intro marker
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  exact namedParameterTail_preservesFile marker.span (some marker.span) name
    (SourceSpan.cover marker.span name.span)

theorem namedParameterCore_preservesFile : Parser.PreservesFile namedParameterCore := by
  intro input
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_preservesFile input
    · exact ordinaryNamedParameter_preservesFile input
  · simpa only [Bool.and_false, Bool.false_eq_true, if_false] using ordinaryNamedParameter_preservesFile input

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem ofFunctionParameter_bind_preservesFile {parser : Parser FunctionParameter}
    (preserved : Parser.PreservesFile parser) :
    Parser.PreservesFile (parser >>= fun parameter => pure (ofFunctionParameter parameter)) :=
  Parser.bind_preservesFile preserved (fun _ => Parser.pure_preservesFile _)

theorem ordinaryLambdaParameterTail_preservesFile (name : Identifier) :
    Parser.PreservesFile (ordinaryLambdaParameterTail name) := by
  unfold ordinaryLambdaParameterTail
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.namedParameterTail_preservesFile name.span none name name.span)
  · exact Parser.pure_preservesFile _

theorem comptimeLambdaParameterTail_preservesFile (marker : Token) (name : Identifier) :
    Parser.PreservesFile (comptimeLambdaParameterTail marker name) := by
  unfold comptimeLambdaParameterTail
  apply Parser.bind_preservesFile getState_preservesFile
  intro observed
  split
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.namedParameterTail_preservesFile marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span))
  · exact ofFunctionParameter_bind_preservesFile
      (FunctionParameterInternals.errorParameter_preservesFile
        (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType)

theorem ordinaryLambdaParameter_preservesFile : Parser.PreservesFile ordinaryLambdaParameter := by
  unfold ordinaryLambdaParameter
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesFile (emitDiagnostic_preservesFile _)
    intro ignored
    exact ordinaryLambdaParameterTail_preservesFile name
  · simp only [warned, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameterTail_preservesFile name

theorem comptimeLambdaParameter_preservesFile : Parser.PreservesFile comptimeLambdaParameter := by
  unfold comptimeLambdaParameter
  apply Parser.bind_preservesFile (contextual_preservesFile .comptime .parameter)
  intro marker
  apply Parser.bind_preservesFile (identifier_preservesFile .parameter)
  intro name
  exact comptimeLambdaParameterTail_preservesFile marker name

theorem lambdaParameterCore_preservesFile : Parser.PreservesFile lambdaParameterCore := by
  intro input
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_preservesFile input
    · exact ordinaryLambdaParameter_preservesFile input
  · simpa only [Bool.and_false, Bool.false_eq_true, if_false] using ordinaryLambdaParameter_preservesFile input

end LambdaParameterInternals

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterTailTraceProperties

/-! Actual ordinary/comptime lambda tails use the same typed tail and a pure
retag. Their absent-colon outcomes differ. These raw-tail laws impose no input
validity and do not cover name dispatch or public recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem ofFunctionParameter_eq_traceValue (parameter : FunctionParameter) :
    ofFunctionParameter parameter = lambdaParameterTraceValue parameter := rfl

theorem ordinaryLambdaParameterTail_eq_of_absent (name : Identifier) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    ordinaryLambdaParameterTail name input = .ok { span := name.span, value := .inferred name } input := by
  simp only [ordinaryLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false, pure]

theorem ordinaryLambdaParameterTail_eq_of_present (name : Identifier) {input : State}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon }) :
    ordinaryLambdaParameterTail name input =
      match namedParameterTail name.span none name name.span input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  rcases present with ⟨span, token⟩
  have colon : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl⟩
  simp only [ordinaryLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon colon, if_true, pure, ofFunctionParameter_eq_traceValue]
  cases namedParameterTail name.span none name name.span input <;> rfl

theorem ordinaryLambdaParameterTail_trace_success_sound (name : Identifier) :
    ParserTraceSuccessSound (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceParses name) := by
  intro input output value result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name present] at result
    cases tailResult : namedParameterTail name.span none name name.span input with
    | invariant error => simp [tailResult] at result
    | reject failure rejected => simp [tailResult] at result
    | ok parameter next =>
        simp only [tailResult] at result
        cases result
        rcases namedParameterTail_trace_success_sound name.span none name name.span tailResult with ⟨trace, tail, events⟩
        exact ⟨trace, .typed present tail, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    rw [ordinaryLambdaParameterTail_eq_of_absent name absent] at result
    cases result
    exact ⟨[], .inferred absent, by simp⟩

theorem ordinaryLambdaParameterTail_reject_trace_sound (name : Identifier) :
    ParserTraceRejectSound (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceRejects name) := by
  intro input rejected failure result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name present] at result
    cases tailResult : namedParameterTail name.span none name name.span input with
    | invariant error => simp [tailResult] at result
    | ok parameter next => simp [tailResult] at result
    | reject actual next =>
        simp only [tailResult] at result
        cases result
        exact namedParameterTail_reject_trace_sound name.span none name name.span tailResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    rw [ordinaryLambdaParameterTail_eq_of_absent name absent] at result
    contradiction

theorem ordinaryLambdaParameterTail_ordinary (name : Identifier) : Parser.Ordinary (ordinaryLambdaParameterTail name) := by
  intro input
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    rw [ordinaryLambdaParameterTail_eq_of_present name
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩]
    rcases namedParameterTail_ordinary name.span none name name.span input with
      ⟨parameter, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨_, output, by rw [result]⟩
    · exact .inr ⟨failure, rejected, by rw [result]⟩
  · exact .inl ⟨_, input, ordinaryLambdaParameterTail_eq_of_absent name
      (symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard))⟩

theorem comptimeLambdaParameterTail_eq_of_absent (marker : Token) (name : Identifier) {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .colon)) :
    comptimeLambdaParameterTail marker name input =
      match errorParameter (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  simp only [comptimeLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_absent .colon absent, Bool.false_eq_true, if_false, pure,
    ofFunctionParameter_eq_traceValue]
  rfl

theorem comptimeLambdaParameterTail_eq_of_present (marker : Token) (name : Identifier) {input : State}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon }) :
    comptimeLambdaParameterTail marker name input =
      match namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
      | .ok parameter output => .ok (lambdaParameterTraceValue parameter) output
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
  rcases present with ⟨span, token⟩
  have colon : ExactTokenParses (.symbol .colon) input.declarativeRemainder span
      { input.declarativeRemainder with cursor := input.cursor + 1 } := ⟨token, rfl⟩
  simp only [comptimeLambdaParameterTail, getState, bind,
    DelimitedTraceInternals.symbol_present .colon colon, if_true, pure, ofFunctionParameter_eq_traceValue]
  cases namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input <;> rfl

theorem comptimeLambdaParameterTail_trace_success_sound (marker : Token) (name : Identifier) :
    ParserTraceSuccessSound (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceParses marker.span name) := by
  intro input output value result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name present] at result
    cases tailResult : namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | invariant error => simp [tailResult] at result
    | reject failure rejected => simp [tailResult] at result
    | ok parameter next =>
        simp only [tailResult] at result
        cases result
        rcases namedParameterTail_trace_success_sound marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span) tailResult with ⟨trace, tail, events⟩
        exact ⟨trace, .typed present tail, events⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult] at result
    cases result
    exact ⟨_, .typeMissing absent .emitted, by
      simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]⟩

theorem comptimeLambdaParameterTail_reject_trace_sound (marker : Token) (name : Identifier) :
    ParserTraceRejectSound (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceRejects marker.span name) := by
  intro input rejected failure result
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    have present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon } :=
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name present] at result
    cases tailResult : namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input with
    | invariant error => simp [tailResult] at result
    | ok parameter next => simp [tailResult] at result
    | reject actual next =>
        simp only [tailResult] at result
        cases result
        exact namedParameterTail_reject_trace_sound marker.span (some marker.span) name
          (SourceSpan.cover marker.span name.span) tailResult
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult] at result
    contradiction

theorem comptimeLambdaParameterTail_ordinary (marker : Token) (name : Identifier) :
    Parser.Ordinary (comptimeLambdaParameterTail marker name) := by
  intro input
  by_cases guard : isSymbol input .colon = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter guard with ⟨colon, colonResult⟩
    rw [comptimeLambdaParameterTail_eq_of_present marker name
      ⟨colon.span, (symbol_ok_tokenAt .colon .parameter colonResult).1⟩]
    rcases namedParameterTail_ordinary marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) input with
      ⟨parameter, output, result⟩ | ⟨failure, rejected, result⟩
    · exact .inl ⟨_, output, by rw [result]⟩
    · exact .inr ⟨failure, rejected, by rw [result]⟩
  · have absent := symbolAbsentAt_of_isSymbol_eq_false .colon (Bool.eq_false_iff.mpr guard)
    have errorResult := errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input .emitted
    exact .inl ⟨_, _, by simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent, errorResult]; rfl⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterTailTraceStateProperties

/-! Exact lambda-tail correspondence determines the whole Reply and State,
including complete uncommitted Failures and arbitrary prior diagnostics.
Retagging changes the AST carrier only, never the returned state or events. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar FunctionParameterInternals

theorem ordinaryLambdaParameterTail_trace_success_state_iff (name : Identifier)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceParses name input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ordinaryLambdaParameterTail name input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | typed present tail =>
        simp only [ordinaryLambdaParameterTail_eq_of_present name present,
          namedParameterTail_eq_ok_of_trace name.span none name name.span tail]
    | inferred absent =>
        rw [ordinaryLambdaParameterTail_eq_of_absent name absent]
        rfl
  · intro result
    rcases ordinaryLambdaParameterTail_trace_success_sound name result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem ordinaryLambdaParameterTail_trace_reject_failure_state_iff (name : Identifier)
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceRejects name input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ordinaryLambdaParameterTail name input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [ordinaryLambdaParameterTail_eq_of_present name rejection.colon_present,
      namedParameterTail_eq_reject_of_trace name.span none name name.span rejection]
  · intro result
    rcases ordinaryLambdaParameterTail_reject_trace_sound name result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem ordinaryLambdaParameterTail_trace_reject_state_iff (name : Identifier)
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTailTraceRejects name input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryLambdaParameterTail name input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete name.span none name name.span rejection with
      ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (ordinaryLambdaParameterTail_trace_reject_failure_state_iff name).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (ordinaryLambdaParameterTail_trace_reject_failure_state_iff name).mpr result

theorem ordinaryLambdaParameterTail_trace_success_complete (name : Identifier) :
    ParserTraceSuccessComplete (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceParses name) := by
  intro input value after trace parsed
  exact ⟨_, (ordinaryLambdaParameterTail_trace_success_state_iff name).mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem ordinaryLambdaParameterTail_trace_reject_complete (name : Identifier) :
    ParserTraceRejectComplete (ordinaryLambdaParameterTail name) (OrdinaryLambdaParameterTailTraceRejects name) := by
  intro input after report trace rejection
  rcases (ordinaryLambdaParameterTail_trace_reject_state_iff name).mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem ordinaryLambdaParameterTail_success_context (name : Identifier) :
    ParserSuccessContext (ordinaryLambdaParameterTail name) := by
  intro input output value result
  have window := ordinaryLambdaParameterTail_preservesTokenWindow name input
  rw [result] at window
  exact ⟨(ordinaryLambdaParameterTail_preservesFile name).file_eq_of_ok result, window.2⟩

theorem ordinaryLambdaParameterTail_reject_context (name : Identifier)
    {input rejected : State} {failure : Failure}
    (result : ordinaryLambdaParameterTail name input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryLambdaParameterTail_preservesTokenWindow name input
  rw [result] at window
  exact ⟨(ordinaryLambdaParameterTail_preservesFile name).file_eq_of_reject result, window.2⟩

theorem ordinaryLambdaParameterTail_ne_invariant (name : Identifier) (input : State) (error : ParserInvariantError) :
    ordinaryLambdaParameterTail name input ≠ .invariant error :=
  (ordinaryLambdaParameterTail_ordinary name).ne_invariant input error

theorem comptimeLambdaParameterTail_trace_success_state_iff (marker : Token) (name : Identifier)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceParses marker.span name input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      comptimeLambdaParameterTail marker name input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | typed present tail =>
        simp only [comptimeLambdaParameterTail_eq_of_present marker name present,
          namedParameterTail_eq_ok_of_trace marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) tail]
    | typeMissing absent finished =>
        simp only [comptimeLambdaParameterTail_eq_of_absent marker name absent,
          errorParameter_eq_ok_of_trace (SourceSpan.cover marker.span name.span) .comptimeParameterRequiresType input finished]
        rfl
  · intro result
    rcases comptimeLambdaParameterTail_trace_success_sound marker name result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

theorem comptimeLambdaParameterTail_trace_reject_failure_state_iff (marker : Token) (name : Identifier)
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceRejects marker.span name input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      comptimeLambdaParameterTail marker name input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    simp only [comptimeLambdaParameterTail_eq_of_present marker name rejection.colon_present,
      namedParameterTail_eq_reject_of_trace marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) rejection]
  · intro result
    rcases comptimeLambdaParameterTail_reject_trace_sound marker name result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using rejection

theorem comptimeLambdaParameterTail_trace_reject_state_iff (marker : Token) (name : Identifier)
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTailTraceRejects marker.span name input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeLambdaParameterTail marker name input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterTail_trace_reject_complete marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, (comptimeLambdaParameterTail_trace_reject_failure_state_iff marker name).mp
      (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ (comptimeLambdaParameterTail_trace_reject_failure_state_iff marker name).mpr result

theorem comptimeLambdaParameterTail_trace_success_complete (marker : Token) (name : Identifier) :
    ParserTraceSuccessComplete (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceParses marker.span name) := by
  intro input value after trace parsed
  exact ⟨_, (comptimeLambdaParameterTail_trace_success_state_iff marker name).mp parsed,
    input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem comptimeLambdaParameterTail_trace_reject_complete (marker : Token) (name : Identifier) :
    ParserTraceRejectComplete (comptimeLambdaParameterTail marker name)
      (ComptimeLambdaParameterTailTraceRejects marker.span name) := by
  intro input after report trace rejection
  rcases (comptimeLambdaParameterTail_trace_reject_state_iff marker name).mp rejection with ⟨failure, result, reportEq⟩
  exact ⟨failure, _, result, input.traceResult_declarativeRemainder after trace, reportEq,
    input.traceResult_diagnostics after trace⟩

theorem comptimeLambdaParameterTail_success_context (marker : Token) (name : Identifier) :
    ParserSuccessContext (comptimeLambdaParameterTail marker name) := by
  intro input output value result
  have window := comptimeLambdaParameterTail_preservesTokenWindow marker name input
  rw [result] at window
  exact ⟨(comptimeLambdaParameterTail_preservesFile marker name).file_eq_of_ok result, window.2⟩

theorem comptimeLambdaParameterTail_reject_context (marker : Token) (name : Identifier)
    {input rejected : State} {failure : Failure}
    (result : comptimeLambdaParameterTail marker name input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := comptimeLambdaParameterTail_preservesTokenWindow marker name input
  rw [result] at window
  exact ⟨(comptimeLambdaParameterTail_preservesFile marker name).file_eq_of_reject result, window.2⟩

theorem comptimeLambdaParameterTail_ne_invariant (marker : Token) (name : Identifier)
    (input : State) (error : ParserInvariantError) : comptimeLambdaParameterTail marker name input ≠ .invariant error :=
  (comptimeLambdaParameterTail_ordinary marker name).ne_invariant input error

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.OrdinaryLambdaParameterTraceProperties

/-! Raw ordinary lambda parameters check the identifier spelling before entering
the tail. All prior events and the complete first failure are retained, without
the selected-core guard or the public parameter recovery policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

theorem ordinaryLambdaParameter_eq_of_checkedName
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    ordinaryLambdaParameter input =
      ordinaryLambdaParameterTail name (input.traceResult after trace) := by
  exact checkedParameterName_continue_of_trace
    (fun name => ordinaryLambdaParameterTail name) parsed

theorem ordinaryLambdaParameter_trace_success_sound :
    ParserTraceSuccessSound ordinaryLambdaParameter OrdinaryLambdaParameterTraceParses := by
  intro input output value result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | reject failure rejected => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryLambdaParameter_eq_of_checkedName headParsed] at result
      rcases ordinaryLambdaParameterTail_trace_success_sound name result with
        ⟨tailEvents, parsed, events⟩
      exact ⟨_, .parsed headParsed parsed, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryLambdaParameter_reject_trace_sound :
    ParserTraceRejectSound ordinaryLambdaParameter OrdinaryLambdaParameterTraceRejects := by
  intro input rejected failure result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryLambdaParameter, bind, nameResult] at result
  | reject actual next =>
      simp only [ordinaryLambdaParameter, bind, nameResult] at result
      cases result
      have same := identifier_reject_state_eq .parameter nameResult
      subst rejected
      have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], .nameRejected reported.1 reported.2, by simp⟩
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryLambdaParameter_eq_of_checkedName headParsed] at result
      rcases ordinaryLambdaParameterTail_reject_trace_sound name result with
        ⟨tailEvents, rejection, events⟩
      exact ⟨_, .tailRejected headParsed rejection, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryLambdaParameter_ordinary : Parser.Ordinary ordinaryLambdaParameter := by
  intro input
  rcases identifier_ordinary .parameter input with ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · rcases identifier_success_trace_sound .parameter result with ⟨nameEvents, identifier, _⟩
    rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
    have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
    rw [ordinaryLambdaParameter_eq_of_checkedName headParsed]
    exact ordinaryLambdaParameterTail_ordinary name _
  · exact .inr ⟨failure, rejected, by simp only [ordinaryLambdaParameter, bind, result]⟩

theorem ordinaryLambdaParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    ordinaryLambdaParameter input ≠ .invariant error := by
  intro failed
  rcases ordinaryLambdaParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem ordinaryLambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete ordinaryLambdaParameter OrdinaryLambdaParameterTraceParses :=
  trace_success_complete_of_sound ordinaryLambdaParameter_trace_success_sound
    ordinaryLambdaParameter_reject_trace_sound (fun _ _ => ordinaryLambdaParameterTraceExactOutcomeSpec)
    ordinaryLambdaParameter_ne_invariant

theorem ordinaryLambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete ordinaryLambdaParameter OrdinaryLambdaParameterTraceRejects :=
  trace_reject_complete_of_sound ordinaryLambdaParameter_trace_success_sound
    ordinaryLambdaParameter_reject_trace_sound (fun _ _ => ordinaryLambdaParameterTraceExactOutcomeSpec)
    ordinaryLambdaParameter_ne_invariant

theorem ordinaryLambdaParameter_success_context : ParserSuccessContext ordinaryLambdaParameter := by
  intro input output value result
  have window := ordinaryLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryLambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem ordinaryLambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : ordinaryLambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryLambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.ComptimeLambdaParameterTraceProperties

/-! The raw comptime path has a silent contextual marker, a checked identifier,
and the comptime lambda tail. The second name never receives the ordinary-name warning.
Marker, name, and tail failures are separate first-failure alternatives. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

theorem comptimeLambdaParameter_trace_success_sound :
    ParserTraceSuccessSound comptimeLambdaParameter ComptimeLambdaParameterTraceParses := by
  intro input output value result
  unfold comptimeLambdaParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases comptimeLambdaParameterTail_trace_success_sound marker name result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .parsed marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeLambdaParameter_reject_trace_sound :
    ParserTraceRejectSound comptimeLambdaParameter ComptimeLambdaParameterTraceRejects := by
  intro input rejected failure result
  unfold comptimeLambdaParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject actual next =>
      simp only [markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.contextual .comptime) .parameter
        (·.isContextual .comptime) markerResult
      subst rejected
      have reported := (contextual_reject_reports_iff .comptime .parameter).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject actual next =>
          simp only [nameResult] at result
          cases result
          have same := identifier_reject_state_eq .parameter nameResult
          subst rejected
          have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
          exact ⟨[], .nameRejected marker.span markerParsed reported.1 reported.2, by simp; rfl⟩
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases comptimeLambdaParameterTail_reject_trace_sound marker name result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .tailRejected marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeLambdaParameter_ordinary : Parser.Ordinary comptimeLambdaParameter := by
  intro input
  rcases contextual_ordinary .comptime .parameter input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · rcases identifier_ordinary .parameter afterMarker with
      ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · rcases comptimeLambdaParameterTail_ordinary marker name next with
        ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
      · exact .inl ⟨value, output, by simp only [comptimeLambdaParameter, bind, markerResult, nameResult, result]⟩
      · exact .inr ⟨failure, rejected, by simp only [comptimeLambdaParameter, bind, markerResult, nameResult, result]⟩
    · exact .inr ⟨failure, rejected, by simp only [comptimeLambdaParameter, bind, markerResult, nameResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [comptimeLambdaParameter, bind, markerResult]⟩

theorem comptimeLambdaParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    comptimeLambdaParameter input ≠ .invariant error := by
  intro failed
  rcases comptimeLambdaParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem comptimeLambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete comptimeLambdaParameter ComptimeLambdaParameterTraceParses :=
  trace_success_complete_of_sound comptimeLambdaParameter_trace_success_sound
    comptimeLambdaParameter_reject_trace_sound (fun _ _ => comptimeLambdaParameterTraceExactOutcomeSpec)
    comptimeLambdaParameter_ne_invariant

theorem comptimeLambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete comptimeLambdaParameter ComptimeLambdaParameterTraceRejects :=
  trace_reject_complete_of_sound comptimeLambdaParameter_trace_success_sound
    comptimeLambdaParameter_reject_trace_sound (fun _ _ => comptimeLambdaParameterTraceExactOutcomeSpec)
    comptimeLambdaParameter_ne_invariant

theorem comptimeLambdaParameter_success_context : ParserSuccessContext comptimeLambdaParameter := by
  intro input output value result
  have window := comptimeLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeLambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem comptimeLambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : comptimeLambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := comptimeLambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeLambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterRawTraceStateProperties

/-! Whole-reply correspondence for both raw lambda-parameter paths. The state
reconstruction keeps every independent remainder field and every prior event;
the diagnostic-report and complete-Failure formulations are both exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

private theorem raw_success_state_iff
    {parser : Parser LambdaParameter}
    {parses : SourceId → Nat → Remainder → LambdaParameter → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound parser parses) (complete : ParserTraceSuccessComplete parser parses)
    (context : ParserSuccessContext parser)
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    parses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      parser input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases complete parsed with ⟨output, result, afterEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact stateEq ▸ result
  · intro result
    rcases sound result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

private theorem raw_reject_state_iff
    {parser : Parser LambdaParameter}
    {rejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (sound : ParserTraceRejectSound parser rejects) (complete : ParserTraceRejectComplete parser rejects)
    (context : ∀ {input rejected failure}, parser input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    rejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, parser input = .reject failure (input.traceResult after trace) ∧ failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases complete rejection with ⟨failure, rejected, result, afterEq, reportEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact ⟨failure, stateEq ▸ result, reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    rcases sound result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, reportEq, ← traceEq] using rejection

theorem ordinaryLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ordinaryLambdaParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff ordinaryLambdaParameter_trace_success_sound ordinaryLambdaParameter_trace_success_complete
    ordinaryLambdaParameter_success_context

theorem ordinaryLambdaParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff ordinaryLambdaParameter_reject_trace_sound ordinaryLambdaParameter_trace_reject_complete
    ordinaryLambdaParameter_reject_context

theorem ordinaryLambdaParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OrdinaryLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ordinaryLambdaParameter input = .reject failure (input.traceResult after trace) := by
  rw [ordinaryLambdaParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

theorem comptimeLambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      comptimeLambdaParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff comptimeLambdaParameter_trace_success_sound comptimeLambdaParameter_trace_success_complete
    comptimeLambdaParameter_success_context

theorem comptimeLambdaParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeLambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff comptimeLambdaParameter_reject_trace_sound comptimeLambdaParameter_trace_reject_complete
    comptimeLambdaParameter_reject_context

theorem comptimeLambdaParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ComptimeLambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      comptimeLambdaParameter input = .reject failure (input.traceResult after trace) := by
  rw [comptimeLambdaParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterCoreTraceProperties

/-! Unconditional exact traces for the non-recovering lambda-parameter core.
The same independent two-token guard chooses each raw success or rejection;
the returned AST, complete State, Failure, and event order are unchanged.
Public rewind and recovery are separate stages. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar ParameterDispatchTraceInternals

theorem lambdaParameterCore_trace_success_sound :
    ParserTraceSuccessSound lambdaParameterCore LambdaParameterCoreTraceParses := by
  intro input output value result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .comptime present parsed, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .ordinary absent parsed, events⟩

theorem lambdaParameterCore_reject_trace_sound :
    ParserTraceRejectSound lambdaParameterCore LambdaParameterCoreTraceRejects := by
  intro input rejected failure result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .comptime present rejection, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .ordinary absent rejection, events⟩

theorem lambdaParameterCore_trace_success_complete :
    ParserTraceSuccessComplete lambdaParameterCore LambdaParameterCoreTraceParses := by
  intro input value after trace parsed
  cases parsed with
  | ordinary absent raw =>
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryLambdaParameter_trace_success_complete raw
  | comptime present raw =>
      rw [lambdaParameterCore_eq_comptime_of_prefix present]
      exact comptimeLambdaParameter_trace_success_complete raw

theorem lambdaParameterCore_trace_reject_complete :
    ParserTraceRejectComplete lambdaParameterCore LambdaParameterCoreTraceRejects := by
  intro input after report trace rejection
  cases rejection with
  | ordinary absent raw =>
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryLambdaParameter_trace_reject_complete raw
  | comptime present raw =>
      rw [lambdaParameterCore_eq_comptime_of_prefix present]
      exact comptimeLambdaParameter_trace_reject_complete raw

theorem lambdaParameterCore_success_context : ParserSuccessContext lambdaParameterCore := by
  intro input output value result
  have window := lambdaParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameterCore_preservesFile.file_eq_of_ok result, window.2⟩

theorem lambdaParameterCore_reject_context {input rejected : State} {failure : Failure}
    (result : lambdaParameterCore input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := lambdaParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameterCore_preservesFile.file_eq_of_reject result, window.2⟩

theorem lambdaParameterCore_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      lambdaParameterCore input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | ordinary absent raw =>
        rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryLambdaParameter_trace_success_state_iff.mp raw
    | comptime present raw =>
        rw [lambdaParameterCore_eq_comptime_of_prefix present]
        exact comptimeLambdaParameter_trace_success_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeLambdaParameter_trace_success_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryLambdaParameter_trace_success_state_iff.mpr result)

theorem lambdaParameterCore_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔ lambdaParameterCore input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    cases rejection with
    | ordinary absent raw =>
        rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryLambdaParameter_trace_reject_failure_state_iff.mp raw
    | comptime present raw =>
        rw [lambdaParameterCore_eq_comptime_of_prefix present]
        exact comptimeLambdaParameter_trace_reject_failure_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [lambdaParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeLambdaParameter_trace_reject_failure_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [lambdaParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryLambdaParameter_trace_reject_failure_state_iff.mpr result)

theorem lambdaParameterCore_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaParameterCore_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, lambdaParameterCore_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ lambdaParameterCore_trace_reject_failure_state_iff.mpr result

theorem lambdaParameterCore_ordinary_unrestricted : Parser.Ordinary lambdaParameterCore := by
  intro input
  by_cases guard : comptimeGuard input = true
  · rw [lambdaParameterCore_eq_comptime_of_prefix (comptimeGuard_true_iff.mp guard)]
    exact comptimeLambdaParameter_ordinary input
  · rw [lambdaParameterCore_eq_ordinary_of_prefix_absent
      (comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard))]
    exact ordinaryLambdaParameter_ordinary input

theorem lambdaParameterCore_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    lambdaParameterCore input ≠ .invariant error := by
  intro failed
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterCoreTraceExistenceProperties

/-! Exact remainder/suffix formulations and non-vacuous outcome existence for
the non-recovering lambda-parameter core. Existence uses ordinary execution
and soundness, not independent uniqueness or success/rejection disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.LambdaParameterInternals

open DeclarativeGrammar

theorem lambdaParameterCore_trace_success_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, lambdaParameterCore input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameterCore_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaParameterCore_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaParameterCore_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, lambdaParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameterCore_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaParameterCore_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaParameterCore_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, lambdaParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, lambdaParameterCore_trace_reject_failure_state_iff.mp rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact lambdaParameterCore_trace_reject_iff.mpr ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaParameterCore_exists_trace_outcome (input : State) :
    (∃ value output trace,
      lambdaParameterCore input = .ok value output ∧
      LambdaParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      lambdaParameterCore input = .reject failure rejected ∧
      LambdaParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaParameterCore_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaParameterCore_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem lambdaParameterCoreTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaParameterCoreTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaParameterCoreTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaParameterCore_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.LambdaParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterTraceProperties

/-! Public lambda parameters retain failed-core events when rewinding the cursor.
Only the non-boundary path commits the core report before standalone recovery.
Ordinary execution is unrestricted and supplies completeness independently of
the declarative uniqueness/disjointness specification. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar LambdaParameterInternals

theorem lambdaParameter_trace_success_sound :
    ParserTraceSuccessSound lambdaParameter LambdaParameterTraceParses := by
  intro input output value result
  cases coreResult : lambdaParameterCore input with
  | ok parameter next =>
      simp only [lambdaParameter, coreResult] at result
      cases result
      rcases lambdaParameterCore_trace_success_sound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases lambdaParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := lambdaParameterCore_reject_context coreResult
      simp only [lambdaParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverLambdaParameter (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverLambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : LambdaParameterRecoveryTraceParses input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            value output.declarativeRemainder trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using parsed
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovered coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [lambdaParameter, coreResult] at result; contradiction

theorem lambdaParameter_reject_trace_sound :
    ParserTraceRejectSound lambdaParameter LambdaParameterTraceRejects := by
  intro input rejected failure result
  cases coreResult : lambdaParameterCore input with
  | ok value next => simp only [lambdaParameter, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases lambdaParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := lambdaParameterCore_reject_context coreResult
      simp only [lambdaParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverLambdaParameter (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (functionParameterBoundaryStops_of_guard_eq_true rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverLambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : LambdaParameterRecoveryTraceRejects input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            rejected.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using rejection
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovery coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [lambdaParameter, coreResult] at result; contradiction

theorem lambdaParameter_preservesFile : Parser.PreservesFile lambdaParameter := by
  intro input
  cases coreResult : lambdaParameterCore input with
  | ok value next =>
      simp only [lambdaParameter, coreResult]
      exact lambdaParameterCore_preservesFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := lambdaParameterCore_preservesFile.file_eq_of_reject coreResult
      simp only [lambdaParameter, coreResult]
      split
      · exact frame
      · exact (recoverLambdaParameter_preservesFile _).trans frame
  | invariant error => simp only [lambdaParameter, coreResult]; trivial

theorem lambdaParameter_success_context : ParserSuccessContext lambdaParameter := by
  intro input output value result
  have window := lambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem lambdaParameter_reject_context {input rejected : State} {failure : Failure}
    (result : lambdaParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := lambdaParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨lambdaParameter_preservesFile.file_eq_of_reject result, window.2⟩

theorem lambdaParameter_ordinary_unrestricted : Parser.Ordinary lambdaParameter := by
  intro input
  rcases lambdaParameterCore_ordinary_unrestricted input with
    ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [lambdaParameter, parsed]⟩
  · simp only [lambdaParameter, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverLambdaParameter_ordinary _

theorem lambdaParameter_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    lambdaParameter input ≠ .invariant error := by
  intro failed
  rcases lambdaParameter_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem lambdaParameter_trace_success_complete :
    ParserTraceSuccessComplete lambdaParameter LambdaParameterTraceParses :=
  trace_success_complete_of_sound lambdaParameter_trace_success_sound lambdaParameter_reject_trace_sound
    (fun _ _ => lambdaParameterTraceExactOutcomeSpec) lambdaParameter_ne_invariant_unrestricted

theorem lambdaParameter_trace_reject_complete :
    ParserTraceRejectComplete lambdaParameter LambdaParameterTraceRejects :=
  trace_reject_complete_of_sound lambdaParameter_trace_success_sound lambdaParameter_reject_trace_sound
    (fun _ _ => lambdaParameterTraceExactOutcomeSpec) lambdaParameter_ne_invariant_unrestricted

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.LambdaParameterTraceStateProperties

/-! The public rewind/recovery trace reconstructs every field of both outcomes,
including the exact terminal Failure separately from committed reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem lambdaParameter_trace_success_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, lambdaParameter input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameter_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases lambdaParameter_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem lambdaParameter_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, lambdaParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact lambdaParameter_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases lambdaParameter_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem lambdaParameter_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, lambdaParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [lambdaParameter_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem lambdaParameter_trace_success_state_iff
    {input : State} {value : LambdaParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    LambdaParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      lambdaParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases lambdaParameter_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := lambdaParameter_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact lambdaParameter_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    LambdaParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      lambdaParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases lambdaParameter_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := lambdaParameter_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact lambdaParameter_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem lambdaParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    LambdaParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, lambdaParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases lambdaParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, lambdaParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ lambdaParameter_trace_reject_failure_state_iff.mpr result

/-! Non-vacuous existence follows from unrestricted ordinary execution and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem lambdaParameter_exists_trace_outcome (input : State) :
    (∃ value output trace,
      lambdaParameter input = .ok value output ∧
      LambdaParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      lambdaParameter input = .reject failure rejected ∧
      LambdaParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases lambdaParameter_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases lambdaParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases lambdaParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem lambdaParameterTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, LambdaParameterTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, LambdaParameterTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases lambdaParameter_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.OrdinaryNamedParameterTraceProperties

/-! Raw ordinary named parameters check the identifier spelling before entering
the tail. All prior events and the complete first failure are retained, without
the selected-core guard or the public parameter recovery policy. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem ordinaryNamedParameter_eq_of_checkedName
    {input : State} {name : Identifier} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : CheckedParameterNameTraceParses input.declarativeRemainder name after trace) :
    ordinaryNamedParameter input =
      namedParameterTail name.span none name name.span (input.traceResult after trace) := by
  exact checkedParameterName_continue_of_trace
    (fun name => namedParameterTail name.span none name name.span) parsed

theorem ordinaryNamedParameter_trace_success_sound :
    ParserTraceSuccessSound ordinaryNamedParameter OrdinaryNamedParameterTraceParses := by
  intro input output value result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryNamedParameter, bind, nameResult] at result
  | reject failure rejected => simp [ordinaryNamedParameter, bind, nameResult] at result
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryNamedParameter_eq_of_checkedName headParsed] at result
      rcases namedParameterTail_trace_success_sound name.span none name name.span result with
        ⟨tailEvents, parsed, events⟩
      exact ⟨_, .parsed headParsed parsed, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryNamedParameter_reject_trace_sound :
    ParserTraceRejectSound ordinaryNamedParameter OrdinaryNamedParameterTraceRejects := by
  intro input rejected failure result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [ordinaryNamedParameter, bind, nameResult] at result
  | reject actual next =>
      simp only [ordinaryNamedParameter, bind, nameResult] at result
      cases result
      have same := identifier_reject_state_eq .parameter nameResult
      subst rejected
      have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
      exact ⟨[], .nameRejected reported.1 reported.2, by simp⟩
  | ok name next =>
      rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, identifier, _⟩
      rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
      have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
      rw [ordinaryNamedParameter_eq_of_checkedName headParsed] at result
      rcases namedParameterTail_reject_trace_sound name.span none name name.span result with
        ⟨tailEvents, rejection, events⟩
      exact ⟨_, .tailRejected headParsed rejection, by
        simpa only [State.traceResult_diagnostics, List.append_assoc] using events⟩

theorem ordinaryNamedParameter_ordinary : Parser.Ordinary ordinaryNamedParameter := by
  intro input
  rcases identifier_ordinary .parameter input with ⟨name, next, result⟩ | ⟨failure, rejected, result⟩
  · rcases identifier_success_trace_sound .parameter result with ⟨nameEvents, identifier, _⟩
    rcases parameterNameFinishingTrace_exists name with ⟨finishEvents, finished⟩
    have headParsed := CheckedParameterNameTraceParses.parsed identifier finished
    rw [ordinaryNamedParameter_eq_of_checkedName headParsed]
    exact namedParameterTail_ordinary name.span none name name.span _
  · exact .inr ⟨failure, rejected, by simp only [ordinaryNamedParameter, bind, result]⟩

theorem ordinaryNamedParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    ordinaryNamedParameter input ≠ .invariant error := by
  intro failed
  rcases ordinaryNamedParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem ordinaryNamedParameter_trace_success_complete :
    ParserTraceSuccessComplete ordinaryNamedParameter OrdinaryNamedParameterTraceParses :=
  trace_success_complete_of_sound ordinaryNamedParameter_trace_success_sound
    ordinaryNamedParameter_reject_trace_sound (fun _ _ => ordinaryNamedParameterTraceExactOutcomeSpec)
    ordinaryNamedParameter_ne_invariant

theorem ordinaryNamedParameter_trace_reject_complete :
    ParserTraceRejectComplete ordinaryNamedParameter OrdinaryNamedParameterTraceRejects :=
  trace_reject_complete_of_sound ordinaryNamedParameter_trace_success_sound
    ordinaryNamedParameter_reject_trace_sound (fun _ _ => ordinaryNamedParameterTraceExactOutcomeSpec)
    ordinaryNamedParameter_ne_invariant

theorem ordinaryNamedParameter_success_context : ParserSuccessContext ordinaryNamedParameter := by
  intro input output value result
  have window := ordinaryNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryNamedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem ordinaryNamedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : ordinaryNamedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := ordinaryNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨ordinaryNamedParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.ComptimeNamedParameterTraceProperties

/-! The raw comptime path has a silent contextual marker, a checked identifier,
and the named tail. The second name never receives the ordinary-name warning.
Marker, name, and tail failures are separate first-failure alternatives. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem comptimeNamedParameter_trace_success_sound :
    ParserTraceSuccessSound comptimeNamedParameter ComptimeNamedParameterTraceParses := by
  intro input output value result
  unfold comptimeNamedParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject failure rejected => simp [markerResult] at result
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases namedParameterTail_trace_success_sound marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .parsed marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeNamedParameter_reject_trace_sound :
    ParserTraceRejectSound comptimeNamedParameter ComptimeNamedParameterTraceRejects := by
  intro input rejected failure result
  unfold comptimeNamedParameter at result
  simp only [bind] at result
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => simp [markerResult] at result
  | reject actual next =>
      simp only [markerResult] at result
      cases result
      have same := acceptToken_reject_state_shape (.contextual .comptime) .parameter
        (·.isContextual .comptime) markerResult
      subst rejected
      have reported := (contextual_reject_reports_iff .comptime .parameter).mpr ⟨failure, markerResult, rfl⟩
      exact ⟨[], .markerMissing reported.1 reported.2, by simp⟩
  | ok marker afterMarker =>
      have markerParsed := contextual_success_exactTokenParses .comptime .parameter markerResult
      have markerState := (contextual_ok_tokenAt .comptime .parameter markerResult).2
      subst afterMarker
      simp only [markerResult] at result
      cases nameResult : identifier .parameter { input with cursor := input.cursor + 1 } with
      | invariant error => simp [nameResult] at result
      | reject actual next =>
          simp only [nameResult] at result
          cases result
          have same := identifier_reject_state_eq .parameter nameResult
          subst rejected
          have reported := (identifier_reject_reports_iff .parameter).mpr ⟨failure, nameResult, rfl⟩
          exact ⟨[], .nameRejected marker.span markerParsed reported.1 reported.2, by simp; rfl⟩
      | ok name next =>
          simp only [nameResult] at result
          rcases identifier_success_trace_sound .parameter nameResult with ⟨nameEvents, nameParsed, nameEventsEq⟩
          have frame := identifier_success_context_eq .parameter nameResult
          rcases namedParameterTail_reject_trace_sound marker.span (some marker.span) name
            (SourceSpan.cover marker.span name.span) result with ⟨tailEvents, tail, tailEventsEq⟩
          refine ⟨nameEvents ++ tailEvents, .tailRejected marker.span markerParsed nameParsed ?_, ?_⟩
          · simpa only [frame.1, frame.2] using tail
          · rw [tailEventsEq, nameEventsEq]
            exact List.append_assoc _ _ _

theorem comptimeNamedParameter_ordinary : Parser.Ordinary comptimeNamedParameter := by
  intro input
  rcases contextual_ordinary .comptime .parameter input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · rcases identifier_ordinary .parameter afterMarker with
      ⟨name, next, nameResult⟩ | ⟨failure, rejected, nameResult⟩
    · rcases namedParameterTail_ordinary marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) next with
        ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
      · exact .inl ⟨value, output, by simp only [comptimeNamedParameter, bind, markerResult, nameResult, result]⟩
      · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult, nameResult, result]⟩
    · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult, nameResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [comptimeNamedParameter, bind, markerResult]⟩

theorem comptimeNamedParameter_ne_invariant (input : State) (error : ParserInvariantError) :
    comptimeNamedParameter input ≠ .invariant error := by
  intro failed
  rcases comptimeNamedParameter_ordinary input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem comptimeNamedParameter_trace_success_complete :
    ParserTraceSuccessComplete comptimeNamedParameter ComptimeNamedParameterTraceParses :=
  trace_success_complete_of_sound comptimeNamedParameter_trace_success_sound
    comptimeNamedParameter_reject_trace_sound (fun _ _ => comptimeNamedParameterTraceExactOutcomeSpec)
    comptimeNamedParameter_ne_invariant

theorem comptimeNamedParameter_trace_reject_complete :
    ParserTraceRejectComplete comptimeNamedParameter ComptimeNamedParameterTraceRejects :=
  trace_reject_complete_of_sound comptimeNamedParameter_trace_success_sound
    comptimeNamedParameter_reject_trace_sound (fun _ _ => comptimeNamedParameterTraceExactOutcomeSpec)
    comptimeNamedParameter_ne_invariant

theorem comptimeNamedParameter_success_context : ParserSuccessContext comptimeNamedParameter := by
  intro input output value result
  have window := comptimeNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeNamedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem comptimeNamedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : comptimeNamedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := comptimeNamedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨comptimeNamedParameter_preservesFile.file_eq_of_reject result, window.2⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterRawTraceStateProperties

/-! Whole-reply correspondence for both raw named-parameter paths. The state
reconstruction keeps every independent remainder field and every prior event;
the diagnostic-report and complete-Failure formulations are both exact. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

private theorem raw_success_state_iff
    {parser : Parser FunctionParameter}
    {parses : SourceId → Nat → Remainder → FunctionParameter → Remainder → List ParseDiagnostic → Prop}
    (sound : ParserTraceSuccessSound parser parses) (complete : ParserTraceSuccessComplete parser parses)
    (context : ParserSuccessContext parser)
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    parses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      parser input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases complete parsed with ⟨output, result, afterEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact stateEq ▸ result
  · intro result
    rcases sound result with ⟨actual, parsed, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, ← traceEq] using parsed

private theorem raw_reject_state_iff
    {parser : Parser FunctionParameter}
    {rejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (sound : ParserTraceRejectSound parser rejects) (complete : ParserTraceRejectComplete parser rejects)
    (context : ∀ {input rejected failure}, parser input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    rejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, parser input = .reject failure (input.traceResult after trace) ∧ failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases complete rejection with ⟨failure, rejected, result, afterEq, reportEq, events⟩
    have frame := context result
    have stateEq := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact ⟨failure, stateEq ▸ result, reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    rcases sound result with ⟨actual, rejection, events⟩
    rw [input.traceResult_diagnostics] at events
    have traceEq := List.append_cancel_left events
    simpa only [State.traceResult_declarativeRemainder, reportEq, ← traceEq] using rejection

theorem ordinaryNamedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ordinaryNamedParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff ordinaryNamedParameter_trace_success_sound ordinaryNamedParameter_trace_success_complete
    ordinaryNamedParameter_success_context

theorem ordinaryNamedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, ordinaryNamedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff ordinaryNamedParameter_reject_trace_sound ordinaryNamedParameter_trace_reject_complete
    ordinaryNamedParameter_reject_context

theorem ordinaryNamedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    OrdinaryNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ordinaryNamedParameter input = .reject failure (input.traceResult after trace) := by
  rw [ordinaryNamedParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

theorem comptimeNamedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      comptimeNamedParameter input = .ok value (input.traceResult after trace) :=
  raw_success_state_iff comptimeNamedParameter_trace_success_sound comptimeNamedParameter_trace_success_complete
    comptimeNamedParameter_success_context

theorem comptimeNamedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, comptimeNamedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report :=
  raw_reject_state_iff comptimeNamedParameter_reject_trace_sound comptimeNamedParameter_trace_reject_complete
    comptimeNamedParameter_reject_context

theorem comptimeNamedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    ComptimeNamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      comptimeNamedParameter input = .reject failure (input.traceResult after trace) := by
  rw [comptimeNamedParameter_trace_reject_state_iff]
  constructor
  · rintro ⟨actual, result, reportEq⟩
    cases Failure.toDiagnostic_injective reportEq
    exact result
  · intro result
    exact ⟨failure, result, rfl⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterCoreTraceProperties

/-! Unconditional exact traces for the non-recovering function-parameter core.
The same independent two-token guard chooses each raw success or rejection;
the returned AST, complete State, Failure, and event order are unchanged.
Public rewind and recovery are separate stages. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar ParameterDispatchTraceInternals

theorem namedParameterCore_trace_success_sound :
    ParserTraceSuccessSound namedParameterCore NamedParameterCoreTraceParses := by
  intro input output value result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [namedParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeNamedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .comptime present parsed, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryNamedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact ⟨trace, .ordinary absent parsed, events⟩

theorem namedParameterCore_reject_trace_sound :
    ParserTraceRejectSound namedParameterCore NamedParameterCoreTraceRejects := by
  intro input rejected failure result
  by_cases guard : comptimeGuard input = true
  · have present := comptimeGuard_true_iff.mp guard
    rw [namedParameterCore_eq_comptime_of_prefix present] at result
    rcases comptimeNamedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .comptime present rejection, events⟩
  · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
    rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
    rcases ordinaryNamedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact ⟨trace, .ordinary absent rejection, events⟩

theorem namedParameterCore_trace_success_complete :
    ParserTraceSuccessComplete namedParameterCore NamedParameterCoreTraceParses := by
  intro input value after trace parsed
  cases parsed with
  | ordinary absent raw =>
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryNamedParameter_trace_success_complete raw
  | comptime present raw =>
      rw [namedParameterCore_eq_comptime_of_prefix present]
      exact comptimeNamedParameter_trace_success_complete raw

theorem namedParameterCore_trace_reject_complete :
    ParserTraceRejectComplete namedParameterCore NamedParameterCoreTraceRejects := by
  intro input after report trace rejection
  cases rejection with
  | ordinary absent raw =>
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
      exact ordinaryNamedParameter_trace_reject_complete raw
  | comptime present raw =>
      rw [namedParameterCore_eq_comptime_of_prefix present]
      exact comptimeNamedParameter_trace_reject_complete raw

theorem namedParameterCore_success_context : ParserSuccessContext namedParameterCore := by
  intro input output value result
  have window := namedParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameterCore_preservesFile.file_eq_of_ok result, window.2⟩

theorem namedParameterCore_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameterCore input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameterCore_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameterCore_preservesFile.file_eq_of_reject result, window.2⟩

theorem namedParameterCore_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      namedParameterCore input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    cases parsed with
    | ordinary absent raw =>
        rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryNamedParameter_trace_success_state_iff.mp raw
    | comptime present raw =>
        rw [namedParameterCore_eq_comptime_of_prefix present]
        exact comptimeNamedParameter_trace_success_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [namedParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeNamedParameter_trace_success_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryNamedParameter_trace_success_state_iff.mpr result)

theorem namedParameterCore_trace_reject_failure_state_iff
    {input : State} {failure : Failure} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔ namedParameterCore input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    cases rejection with
    | ordinary absent raw =>
        rw [namedParameterCore_eq_ordinary_of_prefix_absent absent]
        exact ordinaryNamedParameter_trace_reject_failure_state_iff.mp raw
    | comptime present raw =>
        rw [namedParameterCore_eq_comptime_of_prefix present]
        exact comptimeNamedParameter_trace_reject_failure_state_iff.mp raw
  · intro result
    by_cases guard : comptimeGuard input = true
    · have present := comptimeGuard_true_iff.mp guard
      rw [namedParameterCore_eq_comptime_of_prefix present] at result
      exact .comptime present (comptimeNamedParameter_trace_reject_failure_state_iff.mpr result)
    · have absent := comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard)
      rw [namedParameterCore_eq_ordinary_of_prefix_absent absent] at result
      exact .ordinary absent (ordinaryNamedParameter_trace_reject_failure_state_iff.mpr result)

theorem namedParameterCore_trace_reject_state_iff
    {input : State} {report : ParseDiagnostic} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameterCore input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameterCore_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameterCore_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ namedParameterCore_trace_reject_failure_state_iff.mpr result

theorem namedParameterCore_ordinary_unrestricted : Parser.Ordinary namedParameterCore := by
  intro input
  by_cases guard : comptimeGuard input = true
  · rw [namedParameterCore_eq_comptime_of_prefix (comptimeGuard_true_iff.mp guard)]
    exact comptimeNamedParameter_ordinary input
  · rw [namedParameterCore_eq_ordinary_of_prefix_absent
      (comptimeGuard_false_iff.mp (Bool.eq_false_iff.mpr guard))]
    exact ordinaryNamedParameter_ordinary input

theorem namedParameterCore_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    namedParameterCore input ≠ .invariant error := by
  intro failed
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterCoreTraceExistenceProperties

/-! Exact remainder/suffix formulations and non-vacuous outcome existence for
the non-recovering function-parameter core. Existence uses ordinary execution
and soundness, not independent uniqueness or success/rejection disjointness. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FunctionParameterInternals

open DeclarativeGrammar

theorem namedParameterCore_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder value after trace ↔
      ∃ output, namedParameterCore input = .ok value output ∧
        output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterCore_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameterCore_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameterCore_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameterCore_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameterCore_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameterCore_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
      after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameterCore input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · intro rejection
    exact ⟨_, namedParameterCore_trace_reject_failure_state_iff.mp rejection,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact namedParameterCore_trace_reject_iff.mpr ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameterCore_exists_trace_outcome (input : State) :
    (∃ value output trace,
      namedParameterCore input = .ok value output ∧
      NamedParameterCoreTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      namedParameterCore input = .reject failure rejected ∧
      NamedParameterCoreTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases namedParameterCore_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases namedParameterCore_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem namedParameterCoreTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, NamedParameterCoreTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, NamedParameterCoreTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases namedParameterCore_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser.FunctionParameterInternals

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterTraceProperties

/-! Public named parameters retain failed-core events when rewinding the cursor.
Only the non-boundary path commits the core report before standalone recovery.
Ordinary execution is unrestricted and supplies completeness independently of
the declarative uniqueness/disjointness specification. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar FunctionParameterInternals

theorem namedParameter_trace_success_sound :
    ParserTraceSuccessSound namedParameter NamedParameterTraceParses := by
  intro input output value result
  cases coreResult : namedParameterCore input with
  | ok parameter next =>
      simp only [namedParameter, coreResult] at result
      cases result
      rcases namedParameterCore_trace_success_sound coreResult with ⟨trace, parsed, events⟩
      exact ⟨trace, .core parsed, events⟩
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases namedParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := namedParameterCore_reject_context coreResult
      simp only [namedParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverParameter (rewound.emit original.toDiagnostic)) = .ok value output at result
      split at result
      · contradiction
      · rename_i continues
        rcases recoverParameter_trace_success_sound result with ⟨trace, parsed, events⟩
        have recovery : FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            value output.declarativeRemainder trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using parsed
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovered coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          output.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [namedParameter, coreResult] at result; contradiction

theorem namedParameter_reject_trace_sound :
    ParserTraceRejectSound namedParameter NamedParameterTraceRejects := by
  intro input rejected failure result
  cases coreResult : namedParameterCore input with
  | ok value next => simp only [namedParameter, coreResult] at result; contradiction
  | reject original failed =>
      let rewound := { failed with cursor := input.cursor }
      rcases namedParameterCore_reject_trace_sound coreResult with ⟨coreTrace, coreRejected, coreEvents⟩
      have frame := namedParameterCore_reject_context coreResult
      simp only [namedParameter, coreResult] at result
      change (if rewound.atEnd || isSymbol rewound .comma || isSymbol rewound .rightParen then
        .reject original rewound else recoverParameter (rewound.emit original.toDiagnostic)) =
          .reject failure rejected at result
      split at result
      · rename_i stops
        rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact ⟨coreTrace, .boundary coreRejected
          (functionParameterBoundaryStops_of_guard_eq_true rewound stops), coreEvents⟩
      · rename_i continues
        rcases recoverParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
        have recovery : FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
            (parameterTraceRewind input.declarativeRemainder failed.declarativeRemainder)
            rejected.declarativeRemainder failure.toDiagnostic trace := by
          simpa only [State.emit, rewound, State.declarativeRemainder, parameterTraceRewind,
            frame.1, frame.2] using rejection
        refine ⟨(coreTrace ++ [original.toDiagnostic]) ++ trace,
          .recovery coreRejected
            (no_functionParameterBoundaryStops_of_guard_eq_false rewound (Bool.eq_false_iff.mpr continues)) recovery, ?_⟩
        calc
          rejected.diagnostics = (failed.diagnostics ++ [original.toDiagnostic]) ++ trace := by
            simpa only [State.emit, rewound, State.diagnostics, List.reverse_cons] using events
          _ = input.diagnostics ++ ((coreTrace ++ [original.toDiagnostic]) ++ trace) := by
            rw [coreEvents]
            simp only [List.append_assoc]
  | invariant error => simp only [namedParameter, coreResult] at result; contradiction

theorem namedParameter_preservesFile : Parser.PreservesFile namedParameter := by
  intro input
  cases coreResult : namedParameterCore input with
  | ok value next =>
      simp only [namedParameter, coreResult]
      exact namedParameterCore_preservesFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := namedParameterCore_preservesFile.file_eq_of_reject coreResult
      simp only [namedParameter, coreResult]
      split
      · exact frame
      · exact (recoverParameter_preservesFile _).trans frame
  | invariant error => simp only [namedParameter, coreResult]; trivial

theorem namedParameter_success_context : ParserSuccessContext namedParameter := by
  intro input output value result
  have window := namedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameter_preservesFile.file_eq_of_ok result, window.2⟩

theorem namedParameter_reject_context {input rejected : State} {failure : Failure}
    (result : namedParameter input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have window := namedParameter_preservesTokenWindow input
  rw [result] at window
  exact ⟨namedParameter_preservesFile.file_eq_of_reject result, window.2⟩

theorem namedParameter_ordinary_unrestricted : Parser.Ordinary namedParameter := by
  intro input
  rcases namedParameterCore_ordinary_unrestricted input with
    ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [namedParameter, parsed]⟩
  · simp only [namedParameter, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverParameter_ordinary _

theorem namedParameter_ne_invariant_unrestricted (input : State) (error : ParserInvariantError) :
    namedParameter input ≠ .invariant error := by
  intro failed
  rcases namedParameter_ordinary_unrestricted input with
    ⟨_, _, result⟩ | ⟨_, _, result⟩ <;> rw [result] at failed <;> contradiction

theorem namedParameter_trace_success_complete :
    ParserTraceSuccessComplete namedParameter NamedParameterTraceParses :=
  trace_success_complete_of_sound namedParameter_trace_success_sound namedParameter_reject_trace_sound
    (fun _ _ => namedParameterTraceExactOutcomeSpec) namedParameter_ne_invariant_unrestricted

theorem namedParameter_trace_reject_complete :
    ParserTraceRejectComplete namedParameter NamedParameterTraceRejects :=
  trace_reject_complete_of_sound namedParameter_trace_success_sound namedParameter_reject_trace_sound
    (fun _ _ => namedParameterTraceExactOutcomeSpec) namedParameter_ne_invariant_unrestricted

end Solcore.Syntax.Parser

end

section
-- leanmerge: from Solcore.Syntax.Parser.NamedParameterTraceStateProperties

/-! The public rewind/recovery trace reconstructs every field of both outcomes,
including the exact terminal Failure separately from committed reports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar

theorem namedParameter_trace_success_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      ∃ output, namedParameter input = .ok value output ∧ output.declarativeRemainder = after ∧
        output.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameter_trace_success_complete
  · rintro ⟨output, result, afterEq, events⟩
    rcases namedParameter_trace_success_sound result with ⟨actual, parsed, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, traceEq] using parsed

theorem namedParameter_trace_reject_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure rejected, namedParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
        rejected.diagnostics = input.diagnostics ++ trace := by
  constructor
  · exact namedParameter_trace_reject_complete
  · rintro ⟨failure, rejected, result, afterEq, reportEq, events⟩
    rcases namedParameter_reject_trace_sound result with ⟨actual, rejection, actualEvents⟩
    have traceEq := List.append_cancel_left (actualEvents.symm.trans events)
    simpa only [afterEq, reportEq, traceEq] using rejection

theorem namedParameter_trace_reject_failure_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      ∃ rejected, namedParameter input = .reject failure rejected ∧
        rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace := by
  rw [namedParameter_trace_reject_iff]
  constructor
  · rintro ⟨actual, rejected, result, afterEq, reportEq, events⟩
    cases Failure.toDiagnostic_injective reportEq
    exact ⟨rejected, result, afterEq, events⟩
  · rintro ⟨rejected, result, afterEq, events⟩
    exact ⟨failure, rejected, result, afterEq, rfl, events⟩

theorem namedParameter_trace_success_state_iff
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic} :
    NamedParameterTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace ↔
      namedParameter input = .ok value (input.traceResult after trace) := by
  constructor
  · intro parsed
    rcases namedParameter_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
    have frame := namedParameter_success_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact namedParameter_trace_success_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameter_trace_reject_failure_state_iff
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace ↔
      namedParameter input = .reject failure (input.traceResult after trace) := by
  constructor
  · intro rejection
    rcases namedParameter_trace_reject_failure_iff.mp rejection with ⟨rejected, result, afterEq, events⟩
    have frame := namedParameter_reject_context result
    have same := State.eq_traceResult_of_fields frame.1
      (congrArg TokenWindow.endByte frame.2) afterEq events
    exact same ▸ result
  · intro result
    exact namedParameter_trace_reject_failure_iff.mpr ⟨_, result,
      input.traceResult_declarativeRemainder after trace, input.traceResult_diagnostics after trace⟩

theorem namedParameter_trace_reject_state_iff
    {input : State} {after : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic} :
    NamedParameterTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace ↔
      ∃ failure, namedParameter input = .reject failure (input.traceResult after trace) ∧
        failure.toDiagnostic = report := by
  constructor
  · intro rejection
    rcases namedParameter_trace_reject_complete rejection with ⟨failure, _, _, _, reportEq, _⟩
    exact ⟨failure, namedParameter_trace_reject_failure_state_iff.mp (reportEq.symm ▸ rejection), reportEq⟩
  · rintro ⟨failure, result, reportEq⟩
    exact reportEq ▸ namedParameter_trace_reject_failure_state_iff.mpr result

/-! Non-vacuous existence follows from unrestricted ordinary execution and
soundness, not from the independent joint uniqueness/disjointness laws. -/

theorem namedParameter_exists_trace_outcome (input : State) :
    (∃ value output trace,
      namedParameter input = .ok value output ∧
      NamedParameterTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧ output.diagnostics = input.diagnostics ++ trace) ∨
    (∃ failure rejected trace,
      namedParameter input = .reject failure rejected ∧
      NamedParameterTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧ rejected.diagnostics = input.diagnostics ++ trace) := by
  rcases namedParameter_ordinary_unrestricted input with
    ⟨value, output, result⟩ | ⟨failure, rejected, result⟩
  · rcases namedParameter_trace_success_sound result with ⟨trace, parsed, events⟩
    exact .inl ⟨value, output, trace, result, parsed, events⟩
  · rcases namedParameter_reject_trace_sound result with ⟨trace, rejection, events⟩
    exact .inr ⟨failure, rejected, trace, result, rejection, events⟩

theorem namedParameterTrace_outcome_exists (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ value output trace, NamedParameterTraceParses source endByte input value output trace) ∨
    (∃ rejected report trace, NamedParameterTraceRejects source endByte input rejected report trace) := by
  let state : State := {
    file := { id := source, content := "" }
    tokens := input.tokens
    cursor := input.cursor
    window := { endIndex := input.endIndex, endByte }
    diagnosticsRev := []
  }
  have remainderEq : state.declarativeRemainder = input := rfl
  rcases namedParameter_exists_trace_outcome state with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact .inl ⟨value, output.declarativeRemainder, trace, remainderEq ▸ parsed⟩
  · exact .inr ⟨rejected.declarativeRemainder, failure.toDiagnostic, trace, remainderEq ▸ rejection⟩

end Solcore.Syntax.Parser

end
