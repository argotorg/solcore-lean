import Solcore.Syntax.Parser.LambdaParameterTailTraceStateProperties

/-! Independent lambda-tail witnesses reconstruct complete replies. Missing
colon cases are concrete; typed cases reuse named-tail or recursive type traces
without child execution contracts. Retagging does not replay existing events. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterTailTraceProperties

open Syntax Syntax.Parser Syntax.Parser.LambdaParameterInternals
open Syntax.Parser.FunctionParameterInternals Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "lambda-tail-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def marker : Token := { span := span 0 8, value := .identifier "comptime" }
private def name : Identifier := { span := span 9 12, value := "a-b" }
private def closing : Token := { span := span 12 13, value := .symbol .rightParen }
private def tokens : Array Token := #[marker, { span := name.span, value := .identifier name.value }, closing]
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "comptime a-b)" }, tokens, cursor := 2
  window := { endIndex := 3, endByte := 13 }, diagnosticsRev := prior.reverse
}
private def nameEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def missingEvent : ParseDiagnostic := {
  span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType
}
private def missingValue : LambdaParameter := { span := span 0 12, value := .error }
private def missingOutput (prior : List ParseDiagnostic) : State := {
  input prior with diagnosticsRev := missingEvent :: prior.reverse
}

private theorem colon_absent (prior : List ParseDiagnostic) :
    TokenKindAbsentAt (input prior).tokens (input prior).window.endIndex (input prior).cursor (.symbol .colon) := by
  simp [TokenKindAbsentAt, TokenAt, input, tokens, closing]

/-- An ordinary name before `)` remains inferred. The entire State, including
any already-emitted hyphen warning, is unchanged. The name is not checked again. -/
theorem missing_colon_infers_without_consumption (prior : List ParseDiagnostic) :
    ordinaryLambdaParameterTail name (input prior) =
      .ok { span := name.span, value := .inferred name } (input prior) ∧
    (input prior).diagnostics = prior ∧ (input prior).peek? = some closing := by
  refine ⟨(ordinaryLambdaParameterTail_trace_success_state_iff name (input := input prior)).mp
    (.inferred (colon_absent prior)), ?_, rfl⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- The same absent colon after a comptime marker gives an error-valued
success. Its one event covers marker through name, not the untouched `)`. -/
theorem missing_colon_comptime_emits_cover_error (prior : List ParseDiagnostic) :
    comptimeLambdaParameterTail marker name (input prior) = .ok missingValue (missingOutput prior) ∧
    (missingOutput prior).diagnostics = prior ++ [missingEvent] ∧
    missingValue.span = SourceSpan.cover marker.span name.span ∧
    missingEvent.span = missingValue.span ∧
    (missingOutput prior).cursor = (input prior).cursor ∧
    (missingOutput prior).peek? = some closing := by
  refine ⟨(comptimeLambdaParameterTail_trace_success_state_iff marker name (input := input prior)).mp
    (.typeMissing (colon_absent prior) .emitted), ?_, rfl, rfl, rfl, rfl⟩
  simp only [missingOutput, input, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Two existing copies of the same constraint survive, followed by exactly
one new copy. A pre-existing name event is neither removed nor replayed. -/
theorem missing_type_keeps_prior_duplicates_and_name_event (prior : List ParseDiagnostic) :
    comptimeLambdaParameterTail marker name (input (prior ++ [nameEvent, missingEvent, missingEvent])) =
      .ok missingValue (missingOutput (prior ++ [nameEvent, missingEvent, missingEvent])) ∧
    (missingOutput (prior ++ [nameEvent, missingEvent, missingEvent])).diagnostics =
      prior ++ [nameEvent, missingEvent, missingEvent, missingEvent] := by
  have result := missing_colon_comptime_emits_cover_error (prior ++ [nameEvent, missingEvent, missingEvent])
  refine ⟨result.1, ?_⟩
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1

/-- The ordinary typed branch changes only the FunctionParameter/LambdaParameter
tag. Its name, type, covering span, complete State, and ordered trace are exact. -/
theorem ordinary_typed_named_trace_retags_the_complete_result
    {input : State} {name : Identifier} {type : TypeExpr} {output : Remainder}
    {trace : List ParseDiagnostic}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon })
    (tail : NamedParameterTailTraceParses name.span none name name.span input.file.id input.window.endByte
      input.declarativeRemainder (typedParameterTraceValue name.span none name type) output trace) :
    namedParameterTail name.span none name name.span input =
      .ok (typedParameterTraceValue name.span none name type) (input.traceResult output trace) ∧
    ordinaryLambdaParameterTail name input =
      .ok { span := SourceSpan.cover name.span type.span, value := .typed none name type }
        (input.traceResult output trace) ∧
    (input.traceResult output trace).diagnostics = input.diagnostics ++ trace :=
  ⟨(namedParameterTail_trace_success_state_iff name.span none name name.span).mp tail,
    (ordinaryLambdaParameterTail_trace_success_state_iff name).mp (.typed present tail),
    input.traceResult_diagnostics output trace⟩

/-- The comptime typed branch also retains the explicit marker and all type
ranges. It adds no event beyond the named-tail trace supplied independently. -/
theorem comptime_typed_named_trace_retags_the_complete_result
    {input : State} {marker : Token} {name : Identifier} {type : TypeExpr} {output : Remainder}
    {trace : List ParseDiagnostic}
    (present : ∃ span, TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .colon })
    (tail : NamedParameterTailTraceParses marker.span (some marker.span) name (SourceSpan.cover marker.span name.span)
      input.file.id input.window.endByte input.declarativeRemainder
      (typedParameterTraceValue marker.span (some marker.span) name type) output trace) :
    namedParameterTail marker.span (some marker.span) name (SourceSpan.cover marker.span name.span) input =
      .ok (typedParameterTraceValue marker.span (some marker.span) name type) (input.traceResult output trace) ∧
    comptimeLambdaParameterTail marker name input =
      .ok { span := SourceSpan.cover marker.span type.span, value := .typed (some marker.span) name type }
        (input.traceResult output trace) ∧
    (input.traceResult output trace).diagnostics = input.diagnostics ++ trace :=
  ⟨(namedParameterTail_trace_success_state_iff marker.span (some marker.span) name
      (SourceSpan.cover marker.span name.span)).mp tail,
    (comptimeLambdaParameterTail_trace_success_state_iff marker name).mp (.typed present tail),
    input.traceResult_diagnostics output trace⟩

/-- Both typed tails forward a rejected type's complete Failure and exact
State. The prior prefix is retained, without finishing or report commitment. -/
theorem both_typed_tails_preserve_child_full_failure
    {input : State} {marker : Token} {name : Identifier} {colonSpan : SourceSpan}
    {afterColon rejected : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (colon : ExactTokenParses (.symbol .colon) input.declarativeRemainder colonSpan afterColon)
    (child : TypeExprTraceRejects input.file.id input.window.endByte afterColon
      rejected failure.toDiagnostic trace) :
    ordinaryLambdaParameterTail name input = .reject failure (input.traceResult rejected trace) ∧
    comptimeLambdaParameterTail marker name input = .reject failure (input.traceResult rejected trace) ∧
    (input.traceResult rejected trace).diagnostics = input.diagnostics ++ trace :=
  ⟨(ordinaryLambdaParameterTail_trace_reject_failure_state_iff name).mp (.typeRejected colonSpan colon child),
    (comptimeLambdaParameterTail_trace_reject_failure_state_iff marker name).mp (.typeRejected colonSpan colon child),
    input.traceResult_diagnostics rejected trace⟩

end Solcore.Test.SyntaxLambdaParameterTailTraceProperties
