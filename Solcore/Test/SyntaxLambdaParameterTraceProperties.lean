import Solcore.Syntax.DeclarativeLambdaParameterTraceProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTraceProperties
import Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.LambdaParameterTraceStateProperties
import Solcore.Test.SyntaxLambdaParameterRawTraceProperties

/-! Public lambda-parameter recovery keeps core events when only the cursor is
rewound, commits its original report once, and appends the recovery event last.
Boundary and recovery rejection reports remain separate terminal payloads. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "public-lambda-parameter-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def name : Identifier := { span := span 0 3, value := "a-b" }
private def first : Token := { span := name.span, value := .identifier name.value }
private def skipped : Token := { span := span 6 9, value := .identifier "c-d" }
private def tokens : List Token := [first, symbol 3 4 .colon, symbol 4 5 .plus, skipped, symbol 9 10 .comma]
private def remainder (carrier : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := carrier.toArray, endIndex, cursor
}
private def input (carrier : List Token) (endIndex : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := carrier.toArray, cursor := 0
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def coreFailure : Failure := {
  span := span 4 5, found := some (.symbol .plus), expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}
private def functionRecovered : FunctionParameter := { span := span 0 9, value := .error }
private def recovered : LambdaParameter := { span := span 0 9, value := .error }
private def recoveryEvent : ParseDiagnostic := parameterRecoveryTraceEvent recovered.span
private def events : List ParseDiagnostic := [nameEvent, coreFailure.toDiagnostic, recoveryEvent]
private def final (prior : List ParseDiagnostic) : State := {
  input tokens 5 prior with cursor := 4, diagnosticsRev := events.reverse ++ prior.reverse
}

private theorem scan_continues {before : Remainder} {current : Token}
    (present : TokenAt before.tokens before.endIndex before.cursor current)
    (notComma : current.value ≠ .symbol .comma) (notParen : current.value ≠ .symbol .rightParen) :
    ¬ FunctionParameterRecoveryStops before := by
  intro stops
  cases stops with
  | windowEnd ended => have inside := present.1; omega
  | comma other => exact notComma (congrArg Located.value (present.token_unique other))
  | rightParen other => exact notParen (congrArg Located.value (present.token_unique other))
  | missingToken _ missing => rw [present.2] at missing; contradiction

private theorem nonboundary {before : Remainder} (continues : ¬ FunctionParameterRecoveryStops before) :
    ¬ FunctionParameterBoundaryStops before := by
  intro stops
  cases stops with
  | windowEnd ended => exact continues (.windowEnd ended)
  | comma token => exact continues (.comma token)
  | rightParen token => exact continues (.rightParen token)

private theorem core_rejection : LambdaParameterCoreTraceRejects source 99
    (remainder tokens 5 0) (remainder tokens 5 2) coreFailure.toDiagnostic [nameEvent] := by
  have head : IdentifierTraceParses (remainder tokens 5 0) name (remainder tokens 5 1) [nameEvent] :=
    .parsed ⟨⟨by change 0 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
  have checked : CheckedParameterNameTraceParses (remainder tokens 5 0) name
      (remainder tokens 5 1) [nameEvent] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
      (ParameterNameFinishingTrace.ordinary (by decide))
  have typed : TypeExprTraceRejects source 99 (remainder tokens 5 2) (remainder tokens 5 2)
      coreFailure.toDiagnostic [] :=
    TypeExprTraceRejects.roll (.selected .final
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input tokens 5 [] with cursor := 2 } = .final from rfl))
      (.rejected (.reported (.token (current := symbol 4 5 .plus) ⟨by change 2 < 5; decide, rfl⟩))))
  apply LambdaParameterCoreTraceRejects.ordinary
    (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input tokens 5 []) = false from rfl))
  change OrdinaryLambdaParameterTraceRejects source 99 (remainder tokens 5 0)
    (remainder tokens 5 2) coreFailure.toDiagnostic [nameEvent]
  simpa only [List.append_nil] using OrdinaryLambdaParameterTraceRejects.tailRejected checked
    (.typeRejected (span 3 4) ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩ typed)

private theorem recovery_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder tokens 5 0) functionRecovered (remainder tokens 5 4) [recoveryEvent] := by
  have colon : TokenAt tokens.toArray 5 1 (symbol 3 4 .colon) := ⟨by decide, rfl⟩
  have plus : TokenAt tokens.toArray 5 2 (symbol 4 5 .plus) := ⟨by decide, rfl⟩
  have last : TokenAt tokens.toArray 5 3 skipped := ⟨by decide, rfl⟩
  refine ⟨.recovered (token := first) ⟨by change 0 < 5; decide, rfl⟩ ?_, rfl⟩
  exact .next (scan_continues colon (by decide) (by decide)) colon
    (.next (scan_continues plus (by decide) (by decide)) plus
      (.next (scan_continues last (by decide) (by decide)) last
        (.stop (.comma ⟨by change 4 < 5; decide, rfl⟩))))

private theorem public_recovered_trace : LambdaParameterTraceParses source 99
    (remainder tokens 5 0) recovered (remainder tokens 5 4) events :=
  .recovered core_rejection (nonboundary (scan_continues (current := first)
    ⟨by change 0 < 5; decide, rfl⟩ (by decide) (by decide))) (.recovered recovery_trace)

private def boundaryTokens : List Token := [symbol 0 1 .comma]
private def boundaryFailure : Failure := {
  span := span 0 1, found := some (.symbol .comma)
  expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem boundary_trace : LambdaParameterTraceRejects source 99
    (remainder boundaryTokens 1 0) (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] := by
  have core : LambdaParameterCoreTraceRejects source 99 (remainder boundaryTokens 1 0)
      (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] :=
    .ordinary (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input boundaryTokens 1 []) = false from rfl))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, remainder, boundaryTokens, symbol])
        (.reported (.token (current := symbol 0 1 .comma) ⟨by change 0 < 1; decide, rfl⟩)))
  exact .boundary core (.comma ⟨by change 0 < 1; decide, rfl⟩)

private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .identifier, tail := [] }, context := .parameter
}
private theorem missing_trace : LambdaParameterTraceRejects source 99
    (remainder [] 2 0) (remainder [] 2 0) missingFailure.toDiagnostic [missingFailure.toDiagnostic] := by
  have reported : RejectAtReports source 99 { head := .identifier, tail := [] } .parameter
      (remainder [] 2 0) missingFailure.toDiagnostic :=
    .reported (.missingToken (by change 0 < 2; decide) rfl)
  have core : LambdaParameterCoreTraceRejects source 99 (remainder [] 2 0)
      (remainder [] 2 0) missingFailure.toDiagnostic [] :=
    .ordinary (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input [] 2 []) = false from rfl))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, remainder]) reported)
  have continues : ¬ FunctionParameterBoundaryStops (remainder [] 2 0) := by
    intro stops
    cases stops with
    | windowEnd ended => change 2 ≤ 0 at ended; omega
    | comma token => simp [TokenAt, remainder] at token
    | rightParen token => simp [TokenAt, remainder] at token
  exact .recovery core continues ⟨.missingToken (by change 0 < 2; decide) rfl, reported, rfl⟩

/-- These independent witnesses distinguish a silent boundary rejection from
recovery failure after the same original report has been committed once. -/
theorem independent_public_outcomes :
    LambdaParameterTraceParses source 99 (remainder tokens 5 0) recovered (remainder tokens 5 4) events ∧
    LambdaParameterTraceRejects source 99 (remainder boundaryTokens 1 0)
      (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] ∧
    LambdaParameterTraceRejects source 99 (remainder [] 2 0) (remainder [] 2 0)
      missingFailure.toDiagnostic [missingFailure.toDiagnostic] :=
  ⟨public_recovered_trace, boundary_trace, missing_trace⟩

theorem core_failure_precedes_cursor_rewind (prior : List ParseDiagnostic) :
    LambdaParameterInternals.lambdaParameterCore (input tokens 5 prior) = .reject coreFailure
      { input tokens 5 prior with cursor := 2, diagnosticsRev := nameEvent :: prior.reverse } ∧
    parameterTraceRewind (remainder tokens 5 0) (remainder tokens 5 2) = remainder tokens 5 0 :=
  ⟨(LambdaParameterInternals.lambdaParameterCore_trace_reject_failure_state_iff
    (input := input tokens 5 prior)).mp core_rejection, rfl⟩

/-- Only the cursor is rewound: the checked-name event survives. Recovery
does not check either revisited `a-b` or skipped `c-d` again. -/
theorem public_recovery_retains_order (prior : List ParseDiagnostic) :
    lambdaParameter (input tokens 5 prior) = .ok recovered (final prior) ∧
    (final prior).diagnostics = prior ++ events ∧
    (final prior).peek? = some (symbol 9 10 .comma) := by
  refine ⟨(lambdaParameter_trace_success_state_iff (input := input tokens 5 prior)).mp public_recovered_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem public_recovery_preserves_prior_duplicates (prior : List ParseDiagnostic) :
    lambdaParameter (input tokens 5 (prior ++ [nameEvent, nameEvent])) =
      .ok recovered (final (prior ++ [nameEvent, nameEvent])) ∧
    (final (prior ++ [nameEvent, nameEvent])).diagnostics =
      prior ++ [nameEvent, nameEvent, nameEvent, coreFailure.toDiagnostic, recoveryEvent] := by
  have result := public_recovery_retains_order (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [events, List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

/-- Boundary rejection does not commit the core's terminal report. -/
theorem public_boundary_report_uncommitted (prior : List ParseDiagnostic) :
    lambdaParameter (input boundaryTokens 1 prior) = .reject boundaryFailure (input boundaryTokens 1 prior) ∧
    (input boundaryTokens 1 prior).diagnostics = prior := by
  refine ⟨(lambdaParameter_trace_reject_failure_state_iff
    (input := input boundaryTokens 1 prior)).mp boundary_trace, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- Numeric window membership without backing enters recovery. The core and
recovery reports have equal payloads here, but only the core report is committed. -/
theorem public_recovery_terminal_report_uncommitted (prior : List ParseDiagnostic) :
    lambdaParameter (input [] 2 prior) = .reject missingFailure
      { input [] 2 prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } ∧
    ({ input [] 2 prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } : State).diagnostics =
      prior ++ [missingFailure.toDiagnostic] ∧
    (input [] 2 prior).cursor < (input [] 2 prior).window.endIndex ∧ (input [] 2 prior).peek? = none := by
  refine ⟨(lambdaParameter_trace_reject_failure_state_iff (input := input [] 2 prior)).mp missing_trace,
    ?_, by change 0 < 2; decide, rfl⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Mixed filtering keeps the protected core event while filtering only the
committed original report and recovery event under explicit conditions. -/
theorem recovery_suffix_conditionally_filtered (text : String) (lexical : List SourceSpan)
    (coreSuppressed : LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoverySuppressed : LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events [nameEvent] := by
  have filtered := lambdaParameterRecoveryTrace_cascadeFilters core_rejection text lexical
    (ParseDiagnosticCascadeFilters.drop ⟨by trivial, coreSuppressed⟩ .nil)
    (recovery_trace.cascade_dropped text lexical recoverySuppressed)
  simpa only [events, List.append_nil, List.cons_append, List.nil_append] using filtered

theorem recovery_suffix_retained_without_suppression (text : String) (lexical : List SourceSpan)
    (coreRetained : ¬ LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoveryRetained : ¬ LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events events :=
  lambdaParameterRecoveryTrace_cascadeFilters core_rejection text lexical
    (.keep (fun suppressed => coreRetained suppressed.2) .nil)
    (recovery_trace.cascade_kept text lexical recoveryRetained)

/-- A lexical range covering the recovered region suppresses both cascade
candidates, but the original checked-name diagnostic remains exactly once. -/
theorem mixed_recovery_filter_preserves_only_the_name_event :
    filterParseDiagnostics { id := source, content := "a-b:+ c-d," }
      [{ span := span 0 9, kind := .invalidToken }] events = [nameEvent] :=
  filterParseDiagnostics_eq_of_cascadeFilters _ _
    (recovery_suffix_conditionally_filtered "a-b:+ c-d," [span 0 9]
      ⟨span 0 9, by simp, ⟨rfl, .inr (.inl ⟨by decide, by decide⟩)⟩⟩
      ⟨span 0 9, by simp, ⟨rfl, .inl rfl⟩⟩)

private def stateFrom (owner : SourceId) (endByte : Nat) (before : Remainder)
    (prior : List ParseDiagnostic) : State := {
  file := { id := owner, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte }, diagnosticsRev := prior.reverse
}

private theorem restore_core {owner : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (parsed : LambdaParameterCoreTraceParses owner endByte before value after trace) :
    let s := stateFrom owner endByte before prior
    LambdaParameterInternals.lambdaParameterCore s = .ok value (s.traceResult after trace) ∧
      lambdaParameter s = .ok value (s.traceResult after trace) :=
  ⟨LambdaParameterInternals.lambdaParameterCore_trace_success_state_iff.mp parsed,
    lambdaParameter_trace_success_state_iff.mp (.core parsed)⟩

/-- Reuse the raw `comptime;` witness: ordinary inference is a core success,
so the public parser neither commits a failure nor enters recovery. -/
theorem ordinary_inference_bypasses_recovery (prior : List ParseDiagnostic) :
    ∃ (s : State) (value : LambdaParameter) (after : Remainder) (diagnostic : ParseDiagnostic) (n : Identifier),
      s.diagnostics = prior ∧
      LambdaParameterInternals.lambdaParameterCore s = .ok value (s.traceResult after [diagnostic]) ∧
      lambdaParameter s = .ok value (s.traceResult after [diagnostic]) ∧ value.value = .inferred n ∧
      n.value = "comptime" ∧ diagnostic.kind = .constraintViolation .comptimeUsedAsParameterName ∧
      (s.traceResult after [diagnostic]).diagnostics = prior ++ [diagnostic] ∧
      (s.traceResult after [diagnostic]).peek?.map (·.value) = some (.symbol .semicolon) := by
  have raw := SyntaxLambdaParameterRawTraceProperties.bare_comptime_raw_traces
  have replies := restore_core prior (LambdaParameterCoreTraceParses.ordinary raw.2.2 raw.1)
  refine ⟨_, _, _, _, _, ?_, replies.1, replies.2, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

private theorem comptime_prefix_of_success {owner : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTraceParses owner endByte before value after trace) :
    ComptimeLambdaParameterStartsAt before := by
  cases parsed with
  | parsed markerSpan marker checked _ =>
      rcases marker with ⟨token, rfl⟩
      exact ⟨markerSpan, _, _, token, (identifierTraceParses_iff.mp checked).1.1⟩

/-- Missing type after a marker is a diagnosed core error-value success, not
inference or recovery. The right parenthesis and marker/name cover remain exact. -/
theorem marked_missing_type_bypasses_recovery (prior : List ParseDiagnostic) :
    ∃ (s : State) (value : LambdaParameter) (after : Remainder) (diagnostic : ParseDiagnostic),
      s.diagnostics = prior ∧
      LambdaParameterInternals.lambdaParameterCore s = .ok value (s.traceResult after [diagnostic]) ∧
      lambdaParameter s = .ok value (s.traceResult after [diagnostic]) ∧ value.value = .error ∧
      value.span.startByte = 0 ∧ value.span.endByte = 17 ∧ diagnostic.span = value.span ∧
      diagnostic.kind = .constraintViolation .comptimeParameterRequiresType ∧
      (s.traceResult after [diagnostic]).diagnostics = prior ++ [diagnostic] ∧
      (s.traceResult after [diagnostic]).peek?.map (·.value) = some (.symbol .rightParen) := by
  have raw := SyntaxLambdaParameterRawTraceProperties.marked_missing_trace
  have replies := restore_core prior (LambdaParameterCoreTraceParses.comptime (comptime_prefix_of_success raw) raw)
  refine ⟨_, _, _, _, ?_, replies.1, replies.2, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxLambdaParameterTraceProperties
