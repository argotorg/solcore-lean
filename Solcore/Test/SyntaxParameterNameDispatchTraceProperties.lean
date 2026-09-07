import Solcore.Syntax.Parser.ParameterDispatchTraceProperties
import Solcore.Syntax.Parser.ParameterNameFinishingTraceProperties

/-! Checked ordinary-name events and exact two-token parameter dispatch.
These bounded consumers exercise complete prefix states and branch replies,
without claiming a complete parameter-tail or recovering-parser execution. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParameterNameDispatchTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ParameterDispatchTraceInternals

private def source : SourceId := { origin := .main, path := "parameter-name-dispatch.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def comptimeName : Identifier := { span := span 0 8, value := "comptime" }
private def secondName : Identifier := { span := span 9 17, value := "comptime" }
private def hyphenName : Identifier := { span := span 0 3, value := "a-b" }
private def token (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def warning : ParseDiagnostic := {
  span := comptimeName.span, kind := .constraintViolation .comptimeUsedAsParameterName
}
private def hyphen : ParseDiagnostic := { span := hyphenName.span, kind := .invalidIdentifierHyphen hyphenName.value }
private def later : ParseDiagnostic := { span := span 18 19, kind := .constraintViolation .namedParameterRequiresType }
private def input (tokens : Array Token) (endIndex : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens, cursor := 0
  window := { endIndex, endByte := 77 }, diagnosticsRev := prior.reverse
}
private def pair (endIndex : Nat) (prior : List ParseDiagnostic) : State :=
  input #[token comptimeName, token secondName] endIndex prior
private def nameInput (name : Identifier) (prior : List ParseDiagnostic) : State := input #[token name] 1 prior
private def afterName (name : Identifier) : Remainder := {
  tokens := #[token name], endIndex := 1, cursor := 1
}

private theorem identifier_state {s : State} {name : Identifier} {after : Remainder}
    {trace : List ParseDiagnostic} (parsed : IdentifierTraceParses s.declarativeRemainder name after trace) :
    identifier .parameter s = .ok name (s.traceResult after trace) := by
  rcases (identifier_trace_success_iff .parameter).mp parsed with ⟨output, result, remainderEq, events⟩
  have window := identifier_preservesTokenWindow .parameter s
  rw [result] at window
  have same := State.eq_traceResult_of_fields
    ((identifier_preservesFile .parameter).file_eq_of_ok result)
    (congrArg TokenWindow.endByte window.2) remainderEq events
  exact same ▸ result

/-- Changing only the active end index changes both selected parsers. The
second identifier remains in the same backing array when it is hidden. -/
theorem same_carrier_different_window_changes_both_branches (prior : List ParseDiagnostic) :
    (pair 2 prior).tokens = (pair 1 prior).tokens ∧
    (pair 1 prior).tokens[1]? = some (token secondName) ∧
    (pair 1 prior).peekOffsetKind? 1 = none ∧
    comptimeGuard (pair 2 prior) = true ∧ comptimeGuard (pair 1 prior) = false ∧
    FunctionParameterInternals.namedParameterCore (pair 2 prior) =
      FunctionParameterInternals.comptimeNamedParameter (pair 2 prior) ∧
    FunctionParameterInternals.namedParameterCore (pair 1 prior) =
      FunctionParameterInternals.ordinaryNamedParameter (pair 1 prior) ∧
    LambdaParameterInternals.lambdaParameterCore (pair 2 prior) =
      LambdaParameterInternals.comptimeLambdaParameter (pair 2 prior) ∧
    LambdaParameterInternals.lambdaParameterCore (pair 1 prior) =
      LambdaParameterInternals.ordinaryLambdaParameter (pair 1 prior) := by
  have present := comptimeGuard_true_iff.mp (show comptimeGuard (pair 2 prior) = true from rfl)
  have absent := comptimeGuard_false_iff.mp (show comptimeGuard (pair 1 prior) = false from rfl)
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    FunctionParameterInternals.namedParameterCore_eq_comptime_of_prefix present,
    FunctionParameterInternals.namedParameterCore_eq_ordinary_of_prefix_absent absent,
    LambdaParameterInternals.lambdaParameterCore_eq_comptime_of_prefix present,
    LambdaParameterInternals.lambdaParameterCore_eq_ordinary_of_prefix_absent absent⟩

/-- Being numerically inside the window is insufficient without a token. -/
theorem missing_backing_identifier_chooses_ordinary (prior : List ParseDiagnostic) :
    let s := input #[token comptimeName] 2 prior
    s.cursor + 1 < s.window.endIndex ∧ s.tokens[1]? = none ∧
    comptimeGuard s = false ∧
    FunctionParameterInternals.namedParameterCore s = FunctionParameterInternals.ordinaryNamedParameter s ∧
    LambdaParameterInternals.lambdaParameterCore s = LambdaParameterInternals.ordinaryLambdaParameter s := by
  dsimp only
  have absent := comptimeGuard_false_iff.mp
    (show comptimeGuard (input #[token comptimeName] 2 prior) = false from rfl)
  exact ⟨by change 1 < 2; decide, rfl, rfl,
    FunctionParameterInternals.namedParameterCore_eq_ordinary_of_prefix_absent absent,
    LambdaParameterInternals.lambdaParameterCore_eq_ordinary_of_prefix_absent absent⟩

theorem prior_events_do_not_change_pair_selection (left right : List ParseDiagnostic) (endIndex : Nat) :
    comptimeGuard (pair endIndex left) = comptimeGuard (pair endIndex right) :=
  comptimeGuard_eq_of_remainder_eq rfl

private theorem comptime_prefix_trace (prior : List ParseDiagnostic) :
    CheckedParameterNameTraceParses (nameInput comptimeName prior).declarativeRemainder
      comptimeName (afterName comptimeName) [warning] := by
  have nameTrace : IdentifierTraceParses (nameInput comptimeName prior).declarativeRemainder
      comptimeName (afterName comptimeName) [] :=
    .parsed ⟨⟨by change 0 < 1; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling comptimeName; decide))
  exact .parsed nameTrace (.comptime rfl)

/-- Two earlier equal reports remain, the new warning is appended once, and
the continuation event follows it. No event is deduplicated or reordered. -/
theorem checked_comptime_name_preserves_duplicates_and_order (prior : List ParseDiagnostic) :
    let s := nameInput comptimeName (prior ++ [warning, warning])
    let final := { s with cursor := 1, diagnosticsRev := [later, warning] ++ s.diagnosticsRev }
    (identifier .parameter >>= fun found =>
      if found.value == ContextualKeyword.comptime.spelling then
        emitDiagnostic { span := found.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>=
          fun _ => emitDiagnostic later
      else emitDiagnostic later) s = .ok () final ∧
    final.diagnostics = prior ++ [warning, warning, warning, later] ∧
    ParameterNameFinishingTrace comptimeName [warning] := by
  dsimp only
  constructor
  · exact (checkedParameterName_continue_of_trace (fun _ => emitDiagnostic later)
      (comptime_prefix_trace (prior ++ [warning, warning]))).trans rfl
  · constructor
    · simp only [nameInput, input, State.diagnostics, List.reverse_append, List.reverse_reverse,
        List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]
    · exact .comptime rfl

/-- A hyphen report precedes the continuation without a comptime-name report. -/
theorem checked_hyphen_name_precedes_the_continuation (prior : List ParseDiagnostic) :
    let s := nameInput hyphenName prior
    let final := { s with cursor := 1, diagnosticsRev := [later, hyphen] ++ s.diagnosticsRev }
    (identifier .parameter >>= fun found =>
      if found.value == ContextualKeyword.comptime.spelling then
        emitDiagnostic { span := found.span, kind := .constraintViolation .comptimeUsedAsParameterName } >>=
          fun _ => emitDiagnostic later
      else emitDiagnostic later) s = .ok () final ∧
    final.diagnostics = prior ++ [hyphen, later] ∧ ParameterNameFinishingTrace hyphenName [] := by
  dsimp only
  have nameTrace : IdentifierTraceParses (nameInput hyphenName prior).declarativeRemainder
      hyphenName (afterName hyphenName) [hyphen] :=
    .parsed ⟨⟨by change 0 < 1; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling hyphenName; decide))
  have finishing : ParameterNameFinishingTrace hyphenName [] := .ordinary (by decide)
  have parsed : CheckedParameterNameTraceParses (nameInput hyphenName prior).declarativeRemainder
      hyphenName (afterName hyphenName) [hyphen] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed nameTrace finishing
  refine ⟨(checkedParameterName_continue_of_trace (fun _ => emitDiagnostic later) parsed).trans rfl, ?_, finishing⟩
  simp [nameInput, input, State.diagnostics, List.append_assoc]

/-- In the selected marker branch, even a second spelling `comptime` receives
only identifier checking. Both raw parsers reach their tails with all prior
events unchanged; the ordinary-name finishing check is not run. -/
theorem selected_marker_does_not_warn_about_the_second_comptime_name (prior : List ParseDiagnostic) :
    let s := pair 2 prior
    let next := { s with cursor := 2 }
    FunctionParameterInternals.namedParameterCore s =
      FunctionParameterInternals.namedParameterTail comptimeName.span (some comptimeName.span)
        secondName (SourceSpan.cover comptimeName.span secondName.span) next ∧
    LambdaParameterInternals.lambdaParameterCore s =
      LambdaParameterInternals.comptimeLambdaParameterTail (token comptimeName) secondName next ∧
    next.diagnostics = prior := by
  dsimp only
  have present := comptimeGuard_true_iff.mp (show comptimeGuard (pair 2 prior) = true from rfl)
  have markerResult : contextual .comptime .parameter (pair 2 prior) =
      .ok (token comptimeName) { pair 2 prior with cursor := 1 } :=
    contextual_eq_ok_of_exactTokenParses .comptime .parameter
      ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩
  have nameTrace : IdentifierTraceParses
      ({ pair 2 prior with cursor := 1 } : State).declarativeRemainder secondName
      ({ pair 2 prior with cursor := 2 } : State).declarativeRemainder [] :=
    .parsed ⟨⟨by change 1 < 2; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling secondName; decide))
  have nameResult : identifier .parameter { pair 2 prior with cursor := 1 } =
      .ok secondName { pair 2 prior with cursor := 2 } := identifier_state nameTrace
  constructor
  · rw [FunctionParameterInternals.namedParameterCore_eq_comptime_of_prefix present]
    simp only [FunctionParameterInternals.comptimeNamedParameter, bind, markerResult, nameResult]
    rfl
  · constructor
    · rw [LambdaParameterInternals.lambdaParameterCore_eq_comptime_of_prefix present]
      simp only [LambdaParameterInternals.comptimeLambdaParameter, bind, markerResult, nameResult]
    · simp only [pair, input, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxParameterNameDispatchTraceProperties
