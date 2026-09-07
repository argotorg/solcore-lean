import Solcore.Test.SyntaxParameterListTraceProperties
import Solcore.Syntax.Parser.LambdaParametersTraceProperties

/-! The inline lambda-parameter list uses the same concrete carriers as the
function list, but an untyped ordinary name is inferred rather than erroneous.
Recovery events remain mixed; no unconditional cascade protection is asserted. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterListTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxParameterListTraceProperties

private def inferred : LambdaParameter := { span := name.span, value := .inferred name }
private def recoveredLambda : LambdaParameter := { span := recovered.span, value := .error }

theorem lambda_child {tokens : List Token}
    (present : TokenAt tokens.toArray tokens.length 1 nameToken)
    (absent : TokenKindAbsentAt tokens.toArray tokens.length 2 (.symbol .colon)) :
    LambdaParameterTraceParses source 99 (rem tokens 1) inferred (rem tokens 2) [nameEvent] := by
  apply LambdaParameterTraceParses.core
  apply LambdaParameterCoreTraceParses.ordinary (ordinary_prefix present (by decide))
  simpa only [List.append_nil, inferred] using OrdinaryLambdaParameterTraceParses.parsed
    (checked_name present) (OrdinaryLambdaParameterTailTraceParses.inferred absent)

theorem lambda_one_trace (trailing : Bool) :
    LambdaParametersTraceParses source 99 (rem (oneTokens trailing) 0)
      { span := span 0 6, elements := [inferred] }
      (rem (oneTokens trailing) (oneEnd trailing)) [nameEvent] := by
  apply one_trace _ trailing
  apply lambda_child (tokens := oneTokens trailing) (by cases trailing <;> exact ⟨by decide, rfl⟩)
  cases trailing
  · exact absent_of_token (before := rem (oneTokens false) 2) (token := sym 5 6 .rightParen)
      ⟨by decide, rfl⟩ (by decide)
  · exact absent_of_token (before := rem (oneTokens true) 2) (token := sym 4 5 .comma)
      ⟨by decide, rfl⟩ (by decide)

theorem lambda_missing_trace : LambdaParametersTraceRejects source 99 (rem missingTokens 0)
    (rem missingTokens 2) delimiterFailure.toDiagnostic [nameEvent] := by
  have plus : TokenAt missingTokens.toArray missingTokens.length 2 (sym 4 5 .plus) := ⟨by decide, rfl⟩
  have head : TokenAt missingTokens.toArray missingTokens.length 1 nameToken := ⟨by decide, rfl⟩
  simpa only [List.append_nil, LambdaParametersTraceRejects, delimiterFailure, Failure.toDiagnostic, sym]
    using TrailingDelimitedListTraceRejects.tailRejected (span 0 1)
      (show ExactTokenParses (.symbol .leftParen) (rem missingTokens 0) (span 0 1) (rem missingTokens 1)
        from ⟨⟨by decide, rfl⟩, rfl⟩)
      (.absent (absent_of_token head (by decide)))
      (lambda_child (tokens := missingTokens) head
        (absent_of_token (before := rem missingTokens 2) plus (by decide))) (by change 1 < 2; decide)
      (.delimiterMissing (absent_of_token plus (by decide)) (absent_of_token plus (by decide))
        (.reported (.token (current := sym 4 5 .plus) plus)))

theorem lambda_boundary_trace : LambdaParametersTraceRejects source 99 (rem boundaryTokens 0)
    (rem boundaryTokens 1) (nameFailure .comma).toDiagnostic [] := by
  have comma : TokenAt boundaryTokens.toArray boundaryTokens.length 1 (sym 1 2 .comma) := ⟨by decide, rfl⟩
  have core : LambdaParameterCoreTraceRejects source 99 (rem boundaryTokens 1)
      (rem boundaryTokens 1) (nameFailure .comma).toDiagnostic [] :=
    .ordinary (ordinary_prefix comma (by decide))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, rem, boundaryTokens, sym])
        (.reported (.token (current := sym 1 2 .comma) comma)))
  exact .firstRejected (span 0 1) ⟨⟨by decide, rfl⟩, rfl⟩
    (.absent (absent_of_token comma (by decide))) (.boundary core (.comma comma))

theorem lambda_recovered_trace : LambdaParametersTraceParses source 99 (rem recoveryTokens 0)
    { span := span 0 6, elements := [recoveredLambda] } (rem recoveryTokens 4) recoveryEvents := by
  have plus : TokenAt recoveryTokens.toArray recoveryTokens.length 1 (sym 1 2 .plus) := ⟨by decide, rfl⟩
  have core : LambdaParameterCoreTraceRejects source 99 (rem recoveryTokens 1)
      (rem recoveryTokens 1) (nameFailure .plus).toDiagnostic [] :=
    .ordinary (ordinary_prefix plus (by decide))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, rem, recoveryTokens, sym])
        (.reported (.token (current := sym 1 2 .plus) plus)))
  have child : LambdaParameterTraceParses source 99 (rem recoveryTokens 1) recoveredLambda
      (rem recoveryTokens 2) recoveryEvents :=
    .recovered core recovery_nonboundary (.recovered parameter_recovery_trace)
  simpa only [List.append_nil, LambdaParametersTraceParses, SourceSpan.cover, span, rem]
    using TrailingDelimitedListTraceParses.nonempty (span 0 1) (span 5 6)
      (show ExactTokenParses (.symbol .leftParen) (rem recoveryTokens 0) (span 0 1) (rem recoveryTokens 1)
        from ⟨⟨by decide, rfl⟩, rfl⟩) (.absent (absent_of_token plus (by decide))) child
      (by change 1 < 2; decide) (.trailing (span 4 5) ⟨⟨by decide, rfl⟩, rfl⟩ ⟨⟨by decide, rfl⟩, rfl⟩)

theorem empty_lambda_parameters (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true lambdaParameter .parameter .expression (state emptyTokens prior) =
      .ok { span := span 0 6, elements := [] } ((state emptyTokens prior).traceResult (rem emptyTokens 2) []) :=
  lambdaParameters_trace_success_state_iff.mp (empty_trace _)

theorem single_lambda_parameter (trailing : Bool) (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true lambdaParameter .parameter .expression
      (state (oneTokens trailing) prior) = .ok { span := span 0 6, elements := [inferred] }
        ((state (oneTokens trailing) prior).traceResult (rem (oneTokens trailing) (oneEnd trailing)) [nameEvent]) ∧
    ((state (oneTokens trailing) prior).traceResult (rem (oneTokens trailing) (oneEnd trailing))
      [nameEvent]).peek? = some (sym 6 7 .semicolon) :=
  ⟨lambdaParameters_trace_success_state_iff.mp (lambda_one_trace trailing), by cases trailing <;> rfl⟩

/-- The same carrier emits no named-parameter missing-type event in a lambda. -/
theorem missing_separator_lambda_parameters (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true lambdaParameter .parameter .expression (state missingTokens prior) =
      .reject delimiterFailure ((state missingTokens prior).traceResult (rem missingTokens 2) [nameEvent]) :=
  lambdaParameters_trace_reject_failure_state_iff.mp lambda_missing_trace

theorem first_boundary_lambda_parameters (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true lambdaParameter .parameter .expression (state boundaryTokens prior) =
      .reject (nameFailure .comma) ((state boundaryTokens prior).traceResult (rem boundaryTokens 1) []) :=
  lambdaParameters_trace_reject_failure_state_iff.mp lambda_boundary_trace

theorem recovered_lambda_parameter (prior : List ParseDiagnostic) :
    delimited .leftParen .rightParen true lambdaParameter .parameter .expression
      (state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])) =
      .ok { span := span 0 6, elements := [recoveredLambda] }
        ((state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])).traceResult
          (rem recoveryTokens 4) recoveryEvents) ∧
    ((state recoveryTokens (prior ++ [(nameFailure .plus).toDiagnostic])).traceResult
      (rem recoveryTokens 4) recoveryEvents).diagnostics =
      prior ++ [(nameFailure .plus).toDiagnostic, (nameFailure .plus).toDiagnostic,
        parameterRecoveryTraceEvent recovered.span] := by
  refine ⟨lambdaParameters_trace_success_state_iff.mp lambda_recovered_trace, ?_⟩
  rw [State.traceResult_diagnostics]
  simp only [state, State.diagnostics, List.reverse_reverse, recoveryEvents, List.append_assoc,
    List.cons_append, List.nil_append]

theorem invalid_window_lambda_outcome (prior : List ParseDiagnostic) :
    let input := { state [] prior with cursor := 9, window := { endIndex := 7, endByte := 99 } }
    (∃ value output trace,
      delimited .leftParen .rightParen true lambdaParameter .parameter .expression input = .ok value output ∧
      LambdaParametersTraceParses source 99 input.declarativeRemainder value output.declarativeRemainder trace) ∨
    (∃ failure rejected trace,
      delimited .leftParen .rightParen true lambdaParameter .parameter .expression input = .reject failure rejected ∧
      LambdaParametersTraceRejects source 99 input.declarativeRemainder rejected.declarativeRemainder
        failure.toDiagnostic trace) := by
  dsimp only
  rcases lambdaParameters_exists_trace_outcome
      { state [] prior with cursor := 9, window := { endIndex := 7, endByte := 99 } } with
    ⟨value, output, trace, result, parsed, _⟩ | ⟨failure, rejected, trace, result, rejection, _⟩
  · exact .inl ⟨value, output, trace, result, parsed⟩
  · exact .inr ⟨failure, rejected, trace, result, rejection⟩

end Solcore.Test.SyntaxLambdaParameterListTraceProperties
