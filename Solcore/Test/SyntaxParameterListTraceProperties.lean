import Solcore.Syntax.Parser.FunctionParametersTraceProperties
import Solcore.Syntax.Parser.ParameterDispatchTraceProperties

/-! Concrete independent list witnesses reconstruct whole public replies.
The small token carriers deliberately have no source-content validity premise. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParameterListTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

def source : SourceId := { origin := .main, path := "parameter-list-traces.sol" }
def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
def sym (startByte endByte : Nat) (value : Symbol) : Token :=
  { span := span startByte endByte, value := .symbol value }
def name : Identifier := { span := span 1 4, value := "a-b" }
def nameToken : Token := { span := name.span, value := .identifier name.value }
def rem (tokens : List Token) (cursor : Nat) : Remainder :=
  { tokens := tokens.toArray, endIndex := tokens.length, cursor }
def state (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor := 0
  window := { endIndex := tokens.length, endByte := 99 }, diagnosticsRev := prior.reverse
}
def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
def missingType : ParseDiagnostic := { span := name.span, kind := .constraintViolation .namedParameterRequiresType }
def emptyTokens : List Token := [sym 0 1 .leftParen, sym 5 6 .rightParen, sym 6 7 .semicolon]
def oneTokens (trailing : Bool) : List Token :=
  [sym 0 1 .leftParen, nameToken] ++ (if trailing then [sym 4 5 .comma] else []) ++
    [sym 5 6 .rightParen, sym 6 7 .semicolon]
def oneEnd (trailing : Bool) : Nat := if trailing then 4 else 3
def missingTokens : List Token := [sym 0 1 .leftParen, nameToken, sym 4 5 .plus]
def boundaryTokens : List Token := [sym 0 1 .leftParen, sym 1 2 .comma, sym 5 6 .rightParen]
def recoveryTokens : List Token :=
  [sym 0 1 .leftParen, sym 1 2 .plus, sym 4 5 .comma, sym 5 6 .rightParen, sym 6 7 .semicolon]
def delimiterFailure : Failure := {
  span := span 4 5, found := some (.symbol .plus)
  expected := { head := .symbol .comma, tail := [.symbol .rightParen] }, context := .parameter
}
def nameFailure (kind : Symbol) : Failure := {
  span := span 1 2, found := some (.symbol kind)
  expected := { head := .identifier, tail := [] }, context := .parameter
}
def recovered : FunctionParameter := { span := span 1 2, value := .error }
def recoveryEvents : List ParseDiagnostic :=
  [(nameFailure .plus).toDiagnostic, parameterRecoveryTraceEvent recovered.span]

theorem absent_of_token {before : Remainder} {token : Token} {kind : TokenKind}
    (present : TokenAt before.tokens before.endIndex before.cursor token)
    (different : token.value ≠ kind) :
    TokenKindAbsentAt before.tokens before.endIndex before.cursor kind := by
  rintro ⟨tokenSpan, other⟩
  exact different (congrArg Located.value (present.token_unique other))

theorem ordinary_prefix {before : Remainder} {token : Token}
    (present : TokenAt before.tokens before.endIndex before.cursor token)
    (different : token.value ≠ .identifier ContextualKeyword.comptime.spelling) :
    ComptimeParameterPrefixAbsentAt before := by
  rintro ⟨markerSpan, _, _, marker, _⟩
  exact absent_of_token present different ⟨markerSpan, marker⟩

theorem checked_name {tokens : List Token}
    (present : TokenAt tokens.toArray tokens.length 1 nameToken) :
    CheckedParameterNameTraceParses (rem tokens 1) name (rem tokens 2) [nameEvent] := by
  have head : IdentifierTraceParses (rem tokens 1) name (rem tokens 2) [nameEvent] :=
    .parsed ⟨present, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
  simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
    (.ordinary (by decide))

theorem named_child {tokens : List Token}
    (present : TokenAt tokens.toArray tokens.length 1 nameToken)
    (absent : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .colon)) :
    NamedParameterTraceParses source 99 (rem tokens 1)
      (errorParameterTraceValue name.span) (rem tokens 2) [nameEvent, missingType] :=
  .core (.ordinary (ordinary_prefix present (by decide))
    (.parsed (checked_name present) (.typeMissing absent .emitted)))

theorem empty_trace {α : Type}
    (child : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop) :
    TrailingDelimitedListTraceParses .leftParen .rightParen true child source 99 (rem emptyTokens 0)
      { span := span 0 6, elements := [] } (rem emptyTokens 2) [] :=
  .empty (span 0 1) (span 5 6) rfl ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩
    ⟨⟨by change 1 < 3; decide, rfl⟩, rfl⟩

theorem one_trace {α : Type}
    (child : SourceId → Nat → Remainder → α → Remainder → List ParseDiagnostic → Prop)
    (trailing : Bool) {value : α} {events : List ParseDiagnostic}
    (parsed : child source 99 (rem (oneTokens trailing) 1) value (rem (oneTokens trailing) 2) events) :
    TrailingDelimitedListTraceParses .leftParen .rightParen true child source 99
      (rem (oneTokens trailing) 0) { span := span 0 6, elements := [value] }
      (rem (oneTokens trailing) (oneEnd trailing)) events := by
  have first : TokenAt (oneTokens trailing).toArray (oneTokens trailing).length 1 nameToken := by
    cases trailing <;> exact ⟨by decide, rfl⟩
  have tail : TrailingDelimitedTailTraceParses .rightParen child source 99
      (rem (oneTokens trailing) 2) [] (span 5 6) (rem (oneTokens trailing) (oneEnd trailing)) [] := by
    cases trailing
    · exact .close (absent_of_token (token := sym 5 6 .rightParen) ⟨by decide, rfl⟩ (by decide))
        ⟨⟨by decide, rfl⟩, rfl⟩
    · exact .trailing (span 4 5) ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩
  simpa only [List.append_nil, SourceSpan.cover, span] using TrailingDelimitedListTraceParses.nonempty (span 0 1) (span 5 6)
    (show ExactTokenParses (.symbol .leftParen) (rem (oneTokens trailing) 0) (span 0 1)
      (rem (oneTokens trailing) 1) from ⟨⟨by cases trailing <;> decide, by cases trailing <;> rfl⟩, rfl⟩)
    (.absent (absent_of_token first (by decide))) parsed (by change 1 < 2; decide) tail

theorem named_one_trace (trailing : Bool) :
    FunctionParametersTraceParses source 99 (rem (oneTokens trailing) 0)
      { span := span 0 6, elements := [errorParameterTraceValue name.span] }
      (rem (oneTokens trailing) (oneEnd trailing)) [nameEvent, missingType] := by
  apply one_trace _ trailing
  apply named_child (tokens := oneTokens trailing) (by cases trailing <;> exact ⟨by decide, rfl⟩)
  cases trailing
  · exact absent_of_token (before := rem (oneTokens false) 2) (token := sym 5 6 .rightParen)
      ⟨by decide, rfl⟩ (by decide)
  · exact absent_of_token (before := rem (oneTokens true) 2) (token := sym 4 5 .comma)
      ⟨by decide, rfl⟩ (by decide)

theorem named_missing_trace : FunctionParametersTraceRejects source 99 (rem missingTokens 0)
    (rem missingTokens 2) delimiterFailure.toDiagnostic [nameEvent, missingType] := by
  have plus : TokenAt missingTokens.toArray missingTokens.length 2 (sym 4 5 .plus) := ⟨by decide, rfl⟩
  have head : TokenAt missingTokens.toArray missingTokens.length 1 nameToken := ⟨by decide, rfl⟩
  simpa only [List.append_nil, FunctionParametersTraceRejects, delimiterFailure, Failure.toDiagnostic, sym]
    using TrailingDelimitedListTraceRejects.tailRejected (span 0 1)
    (show ExactTokenParses (.symbol .leftParen) (rem missingTokens 0) (span 0 1) (rem missingTokens 1)
      from ⟨⟨by decide, rfl⟩, rfl⟩)
    (.absent (absent_of_token head (by decide)))
    (named_child (tokens := missingTokens) head
      (absent_of_token (before := rem missingTokens 2) plus (by decide))) (by change 1 < 2; decide)
    (.delimiterMissing (absent_of_token plus (by decide)) (absent_of_token plus (by decide))
      (.reported (.token (current := sym 4 5 .plus) plus)))

theorem named_boundary_trace : FunctionParametersTraceRejects source 99 (rem boundaryTokens 0)
    (rem boundaryTokens 1) (nameFailure .comma).toDiagnostic [] := by
  have comma : TokenAt boundaryTokens.toArray boundaryTokens.length 1 (sym 1 2 .comma) := ⟨by decide, rfl⟩
  have core : NamedParameterCoreTraceRejects source 99 (rem boundaryTokens 1)
      (rem boundaryTokens 1) (nameFailure .comma).toDiagnostic [] :=
    .ordinary (ordinary_prefix comma (by decide))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, rem, boundaryTokens, sym])
        (.reported (.token (current := sym 1 2 .comma) comma)))
  exact .firstRejected (span 0 1) ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (absent_of_token comma (by decide))) (.boundary core (.comma comma))

theorem recovery_nonboundary : ¬ FunctionParameterBoundaryStops (rem recoveryTokens 1) := by
  intro stops
  cases stops with
  | windowEnd ended => change 5 ≤ 1 at ended; omega
  | comma token => simp [TokenAt, rem, recoveryTokens, sym] at token
  | rightParen token => simp [TokenAt, rem, recoveryTokens, sym] at token

theorem parameter_recovery_trace : FunctionParameterRecoveryTraceParses source 99
    (rem recoveryTokens 1) recovered (rem recoveryTokens 2) [parameterRecoveryTraceEvent recovered.span] :=
  ⟨.recovered (token := sym 1 2 .plus) ⟨by decide, rfl⟩
    (.stop (.comma ⟨by decide, rfl⟩)), rfl⟩

theorem named_recovered_trace : FunctionParametersTraceParses source 99 (rem recoveryTokens 0)
    { span := span 0 6, elements := [recovered] } (rem recoveryTokens 4) recoveryEvents := by
  have plus : TokenAt recoveryTokens.toArray recoveryTokens.length 1 (sym 1 2 .plus) := ⟨by decide, rfl⟩
  have core : NamedParameterCoreTraceRejects source 99 (rem recoveryTokens 1)
      (rem recoveryTokens 1) (nameFailure .plus).toDiagnostic [] :=
    .ordinary (ordinary_prefix plus (by decide))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, rem, recoveryTokens, sym])
        (.reported (.token (current := sym 1 2 .plus) plus)))
  have child : NamedParameterTraceParses source 99 (rem recoveryTokens 1) recovered
      (rem recoveryTokens 2) recoveryEvents := .recovered core recovery_nonboundary parameter_recovery_trace
  simpa only [List.append_nil, FunctionParametersTraceParses, SourceSpan.cover, span, rem]
    using TrailingDelimitedListTraceParses.nonempty (span 0 1) (span 5 6)
    (show ExactTokenParses (.symbol .leftParen) (rem recoveryTokens 0) (span 0 1) (rem recoveryTokens 1)
      from ⟨⟨by decide, rfl⟩, rfl⟩) (.absent (absent_of_token plus (by decide))) child
    (by change 1 < 2; decide) (.trailing (span 4 5) ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩)

theorem empty_function_parameters (prior : List ParseDiagnostic) :
    functionParameters (state emptyTokens prior) = .ok { span := span 0 6, elements := [] }
      ((state emptyTokens prior).traceResult (rem emptyTokens 2) []) :=
  functionParameters_trace_success_state_iff.mp (empty_trace _)

theorem single_function_parameter (trailing : Bool) (prior : List ParseDiagnostic) :
    functionParameters (state (oneTokens trailing) prior) =
      .ok { span := span 0 6, elements := [errorParameterTraceValue name.span] }
        ((state (oneTokens trailing) prior).traceResult (rem (oneTokens trailing) (oneEnd trailing))
          [nameEvent, missingType]) ∧
    ((state (oneTokens trailing) prior).traceResult (rem (oneTokens trailing) (oneEnd trailing))
      [nameEvent, missingType]).peek? = some (sym 6 7 .semicolon) :=
  ⟨functionParameters_trace_success_state_iff.mp (named_one_trace trailing), by cases trailing <;> rfl⟩

/-- Comma is the first expected delimiter; the terminal report is not committed. -/
theorem missing_separator_function_parameters (prior : List ParseDiagnostic) :
    functionParameters (state missingTokens prior) = .reject delimiterFailure
      ((state missingTokens prior).traceResult (rem missingTokens 2) [nameEvent, missingType]) :=
  functionParameters_trace_reject_failure_state_iff.mp named_missing_trace

theorem first_boundary_function_parameters (prior : List ParseDiagnostic) :
    functionParameters (state boundaryTokens prior) = .reject (nameFailure .comma)
      ((state boundaryTokens prior).traceResult (rem boundaryTokens 1) []) :=
  functionParameters_trace_reject_failure_state_iff.mp named_boundary_trace

/-- A prior equal report survives, followed by the child's committed report and recovery event. -/
theorem recovered_function_parameter (prior : List ParseDiagnostic) :
    functionParameters (state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])) =
      .ok { span := span 0 6, elements := [recovered] }
        ((state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])).traceResult
          (rem recoveryTokens 4) recoveryEvents) ∧
    ((state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])).traceResult
      (rem recoveryTokens 4) recoveryEvents).diagnostics =
      prior ++ [(nameFailure .plus).toDiagnostic, (nameFailure .plus).toDiagnostic,
        parameterRecoveryTraceEvent recovered.span] := by
  refine ⟨functionParameters_trace_success_state_iff.mp named_recovered_trace, ?_⟩
  rw [State.traceResult_diagnostics]
  simp only [state, State.diagnostics, List.reverse_reverse, recoveryEvents, List.append_assoc,
    List.cons_append, List.nil_append]

theorem invalid_window_function_outcome (prior : List ParseDiagnostic) :
    let input := { state [] prior with cursor := 9, window := { endIndex := 7, endByte := 99 } }
    (∃ value output trace, functionParameters input = .ok value output ∧
      FunctionParametersTraceParses source 99 input.declarativeRemainder value output.declarativeRemainder trace) ∨
    (∃ failure rejected trace, functionParameters input = .reject failure rejected ∧
      FunctionParametersTraceRejects source 99 input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace) := by
  dsimp only
  rcases functionParameters_exists_trace_outcome
      { state [] prior with cursor := 9, window := { endIndex := 7, endByte := 99 } } with
    ⟨value, output, trace, result, parsed, _⟩ | ⟨failure, rejected, trace, result, rejection, _⟩
  · exact .inl ⟨value, output, trace, result, parsed⟩
  · exact .inr ⟨failure, rejected, trace, result, rejection⟩

end Solcore.Test.SyntaxParameterListTraceProperties
