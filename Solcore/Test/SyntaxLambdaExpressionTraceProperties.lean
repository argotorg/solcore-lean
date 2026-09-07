import Solcore.Syntax.Parser.LambdaExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceStateProperties
import Solcore.Syntax.DeclarativeLambdaExpressionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.CoreBlockClosingTraceProperties

/-! Raw lambda consumers retain a recovering parameter prefix before the
return and supplied body. Body results are explicit pointwise assumptions;
no general recursive block trace contract is claimed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaExpressionTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open ExpressionAtomInternals

private def source : SourceId := { origin := .main, path := "raw-lambda-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def token (startByte endByte : Nat) (value : TokenKind) : Token := { span := span startByte endByte, value }
private def marker : Token := token 0 3 (.keyword .lamKw)
private def tokens (returnKind : TokenKind) : List Token := [marker, token 3 4 (.symbol .leftParen),
  token 4 5 (.symbol .plus), token 5 6 (.symbol .rightParen), token 7 9 (.symbol .arrow),
  token 10 13 returnKind, token 14 15 (.symbol .leftBrace), token 15 16 (.symbol .rightBrace), token 16 17 (.symbol .semicolon)]
private def remainder (kind : TokenKind) (cursor : Nat) : Remainder := {
  tokens := (tokens kind).toArray, endIndex := 9, cursor
}
private def state (kind : TokenKind) (cursor : Nat) (events prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := (tokens kind).toArray, cursor
  window := { endIndex := 9, endByte := 17 }, diagnosticsRev := events.reverse ++ prior.reverse
}
private def parameterFailure : Failure := {
  span := span 4 5, found := some (.symbol .plus), expected := { head := .identifier, tail := [] }, context := .parameter
}
private def parameter : LambdaParameter := { span := span 4 5, value := .error }
private def parameters : DelimitedList LambdaParameter := { span := span 3 6, elements := [parameter] }
private def parameterEvents : List ParseDiagnostic :=
  [parameterFailure.toDiagnostic, parameterRecoveryTraceEvent parameter.span]
private def name : Identifier := { span := span 10 13, value := "a-b" }
private def returnType : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def returnEvent : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def prefixEvents : List ParseDiagnostic := parameterEvents ++ [returnEvent]
private def typedKind : TokenKind := .identifier name.value

private theorem parameters_trace (kind : TokenKind) : LambdaParametersTraceParses source 17
    (remainder kind 1) parameters (remainder kind 4) parameterEvents := by
  have core : LambdaParameterCoreTraceRejects source 17 (remainder kind 2)
      (remainder kind 2) parameterFailure.toDiagnostic [] :=
    .ordinary (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (state kind 2 [] []) = false from rfl))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, remainder, tokens, token])
        (.reported (.token (current := token 4 5 (.symbol .plus)) ⟨by change 2 < 9; decide, rfl⟩)))
  have continues : ¬ FunctionParameterBoundaryStops (remainder kind 2) := by
    intro stops
    cases stops with
    | windowEnd ended => change 9 ≤ 2 at ended; omega
    | comma present => simp [TokenAt, remainder, tokens, token] at present
    | rightParen present => simp [TokenAt, remainder, tokens, token] at present
  have recovery : FunctionParameterRecoveryTraceParses source 17 (remainder kind 2)
      ({ span := span 4 5, value := .error } : FunctionParameter) (remainder kind 3)
      [parameterRecoveryTraceEvent parameter.span] :=
    ⟨.recovered (token := token 4 5 (.symbol .plus)) ⟨by change 2 < 9; decide, rfl⟩
      (.stop (.rightParen ⟨by change 3 < 9; decide, rfl⟩)), rfl⟩
  have child : LambdaParameterTraceParses source 17 (remainder kind 2) parameter
      (remainder kind 3) parameterEvents := .recovered core continues (.recovered recovery)
  have parsed : LambdaParametersTraceParses source 17 (remainder kind 1) parameters
      (remainder kind 4) (parameterEvents ++ []) := .nonempty
    (afterOpening := remainder kind 2) (afterFirst := remainder kind 3) (rest := [])
    (span 3 4) (span 5 6) ⟨⟨by change 1 < 9; decide, rfl⟩, rfl⟩
    (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, token])) child (by change 2 < 3; decide)
    (.close (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, token]) ⟨⟨by change 3 < 9; decide, rfl⟩, rfl⟩)
  simpa only [List.append_nil] using parsed

private theorem return_trace : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses source 17
    (remainder typedKind 4) (some returnType) (remainder typedKind 6) [returnEvent] := by
  have checked : IdentifierTraceParses (remainder typedKind 5) name (remainder typedKind 6) [returnEvent] :=
    .parsed ⟨⟨by change 5 < 9; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
  have qualified : QualifiedNameTraceParses source 17 (remainder typedKind 5)
      (tracedQualifiedName name []) (remainder typedKind 6) [returnEvent] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed checked
      (.done (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, token]))
  have named : NamedTypeTraceParses TypeExprTraceParses source 17 (remainder typedKind 5)
      returnType (remainder typedKind 6) [returnEvent] := by
    simpa only [returnType, List.append_nil] using NamedTypeTraceParses.parsed qualified
      (.absent (by simp [TokenKindAbsentAt, TokenAt, remainder, tokens, token]))
      (.ordinary (by unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix name; decide))
  exact .present (span 7 9) ⟨⟨by change 4 < 9; decide, rfl⟩, rfl⟩
    (TypeExprTraceParses.roll (.selected .named
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state typedKind 5 [] []) = .named from rfl)) named))

private theorem optional_return_state {input : State} {value : Option TypeExpr} {after : Remainder}
    {trace : List ParseDiagnostic} (parsed : OptionalLambdaReturnTypeTraceParses TypeExprTraceParses
      input.file.id input.window.endByte input.declarativeRemainder value after trace) :
    optionalLambdaReturnType input = .ok value (input.traceResult after trace) := by
  rcases optionalLambdaReturnType_concrete_trace_success_complete parsed with ⟨output, result, afterEq, events⟩
  have frame := optionalLambdaReturnType_concrete_success_context result
  exact State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events ▸ result

private theorem marker_result (kind : TokenKind) (prior : List ParseDiagnostic) :
    keyword .lamKw .expression (state kind 0 [] prior) = .ok marker (state kind 1 [] prior) :=
  keyword_eq_ok_of_exactTokenParses .lamKw .expression ⟨⟨by change 0 < 9; decide, rfl⟩, rfl⟩

private theorem parameters_result (kind : TokenKind) (prior : List ParseDiagnostic) :
    (delimited .leftParen .rightParen true lambdaParameter .parameter .expression) (state kind 1 [] prior) =
      .ok parameters (state kind 4 parameterEvents prior) :=
  (lambdaParameters_trace_success_state_iff (input := state kind 1 [] prior)).mp (parameters_trace kind)

private theorem return_result (prior : List ParseDiagnostic) :
    optionalLambdaReturnType (state typedKind 4 parameterEvents prior) =
      .ok (some returnType) (state typedKind 6 prefixEvents prior) :=
  optional_return_state (input := state typedKind 4 parameterEvents prior) return_trace

/-- The supplied body runs after both recovery events and the checked return
name. Its exact AST and complete output State are retained without alteration. -/
theorem typed_success_keeps_all_components {block : Parser Block} (prior : List ParseDiagnostic)
    (body : Block) (output : State)
    (bodyResult : block (state typedKind 6 prefixEvents prior) = .ok body output) :
    lambdaExpression block (state typedKind 0 [] prior) =
      .ok (lambdaExpressionTraceValue (span 0 3) parameters (some returnType) body) output ∧
    (lambdaExpressionTraceValue (span 0 3) parameters (some returnType) body).value =
      .lambda (span 0 3) parameters (some returnType) body ∧
    (state typedKind 6 prefixEvents prior).diagnostics = prior ++ prefixEvents := by
  refine ⟨lambdaExpression_success_iff_components.mpr ⟨_, _, _, _, _, _, _, marker_result _ prior,
    parameters_result _ prior, return_result prior, bodyResult, rfl⟩, rfl, ?_⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem body_failure_keeps_prefix_and_full_failure {block : Parser Block} (prior : List ParseDiagnostic)
    (failure : Failure) (rejected : State)
    (bodyResult : block (state typedKind 6 prefixEvents prior) = .reject failure rejected) :
    lambdaExpression block (state typedKind 0 [] prior) = .reject failure rejected :=
  lambdaExpression_eq_reject_of_body (marker_result _ prior) (parameters_result _ prior) (return_result prior) bodyResult

theorem typed_success_orders_body_events {block : Parser Block} (prior bodyEvents : List ParseDiagnostic)
    (body : Block) (after : Remainder)
    (bodyResult : block (state typedKind 6 prefixEvents prior) =
      .ok body ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents)) :
    lambdaExpression block (state typedKind 0 [] prior) =
      .ok (lambdaExpressionTraceValue (span 0 3) parameters (some returnType) body)
        ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents) ∧
    ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents).diagnostics =
      prior ++ (parameterEvents ++ [returnEvent] ++ bodyEvents) ∧
    (lambdaExpressionTraceValue (span 0 3) parameters (some returnType) body).span =
      SourceSpan.cover (span 0 3) body.span := by
  refine ⟨(typed_success_keeps_all_components prior body _ bodyResult).1, ?_, rfl⟩
  rw [State.traceResult_diagnostics]
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse, prefixEvents, List.append_assoc]

/-- Body-local events follow both the recovering parameter and return events.
The terminal Failure is returned separately and is not appended here. -/
theorem body_failure_orders_events {block : Parser Block} (prior bodyEvents : List ParseDiagnostic)
    (failure : Failure) (after : Remainder)
    (bodyResult : block (state typedKind 6 prefixEvents prior) =
      .reject failure ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents)) :
    lambdaExpression block (state typedKind 0 [] prior) =
      .reject failure ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents) ∧
    ((state typedKind 6 prefixEvents prior).traceResult after bodyEvents).diagnostics =
      prior ++ (parameterEvents ++ [returnEvent] ++ bodyEvents) := by
  refine ⟨body_failure_keeps_prefix_and_full_failure prior failure _ bodyResult, ?_⟩
  rw [State.traceResult_diagnostics]
  simp only [state, State.diagnostics, List.reverse_append,
    List.reverse_reverse, prefixEvents, List.append_assoc]

private def markerFailure : Failure := {
  parameterFailure with expected := { head := .keyword .lamKw, tail := [] }, context := .expression
}

theorem missing_marker_bypasses_any_body (block : Parser Block) (prior : List ParseDiagnostic) :
    lambdaExpression block (state typedKind 2 [] prior) = .reject markerFailure (state typedKind 2 [] prior) := by
  have reported : TokenKindAbsentAt (tokens typedKind).toArray 9 2 (.keyword .lamKw) ∧
      RejectAtReports source 17 { head := .keyword .lamKw, tail := [] } .expression
        (remainder typedKind 2) markerFailure.toDiagnostic :=
    ⟨by simp [TokenKindAbsentAt, TokenAt, tokens, token, marker],
      .reported (.token (current := token 4 5 (.symbol .plus)) ⟨by decide, rfl⟩)⟩
  rcases (keyword_reject_reports_iff .lamKw .expression (input := state typedKind 2 [] prior)).mp reported with
    ⟨actual, result, reportEq⟩
  exact lambdaExpression_eq_reject_of_marker (Failure.toDiagnostic_injective reportEq ▸ result)

private def shortState (cursor : Nat) (prior : List ParseDiagnostic) : State :=
  { state typedKind cursor [] prior with window := { endIndex := 1, endByte := 17 } }
private def openingFailure : Failure := {
  span := span 17 17, found := none, expected := { head := .symbol .leftParen, tail := [] }, context := .parameter
}

/-- The backing opening token exists but is hidden by the active window. -/
theorem hidden_opening_bypasses_any_body (block : Parser Block) (prior : List ParseDiagnostic) :
    lambdaExpression block (shortState 0 prior) = .reject openingFailure (shortState 1 prior) ∧
    (shortState 1 prior).tokens[1]? = some (token 3 4 (.symbol .leftParen)) ∧
    (shortState 1 prior).diagnostics = prior := by
  have markerResult : keyword .lamKw .expression (shortState 0 prior) = .ok marker (shortState 1 prior) :=
    keyword_eq_ok_of_exactTokenParses .lamKw .expression ⟨⟨by change 0 < 1; decide, rfl⟩, rfl⟩
  have rejected : LambdaParametersTraceRejects source 17 (shortState 1 prior).declarativeRemainder
      (shortState 1 prior).declarativeRemainder openingFailure.toDiagnostic [] :=
    .openingMissing (by intro ⟨_, before, _⟩; change 1 < 1 at before; omega)
      (.reported (.windowEnd (by change 1 ≤ 1; decide)))
  refine ⟨lambdaExpression_eq_reject_of_parameters markerResult
    ((lambdaParameters_trace_reject_failure_state_iff (input := shortState 1 prior)).mp rejected), rfl, ?_⟩
  simp only [shortState, state, State.diagnostics, List.reverse_nil, List.nil_append, List.reverse_reverse]

private def returnFailure : Failure := {
  span := span 10 13, found := some (.symbol .plus), expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}
private theorem return_rejection : OptionalLambdaReturnTypeTraceRejects TypeExprTraceRejects source 17
    (remainder (.symbol .plus) 4) (remainder (.symbol .plus) 5) returnFailure.toDiagnostic [] :=
  .typeRejected (span 7 9) ⟨⟨by change 4 < 9; decide, rfl⟩, rfl⟩
    (TypeExprTraceRejects.roll (.selected .final
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state (.symbol .plus) 5 [] []) = .final from rfl))
      (.rejected (.reported (.token (current := token 10 13 (.symbol .plus)) ⟨by change 5 < 9; decide, rfl⟩)))))

/-- Recovery's committed report and event survive a later return-type failure;
that new terminal report remains uncommitted and the body is never invoked. -/
theorem return_failure_keeps_recovery_before_any_body (block : Parser Block) (prior : List ParseDiagnostic) :
    lambdaExpression block (state (.symbol .plus) 0 [] prior) =
      .reject returnFailure (state (.symbol .plus) 5 parameterEvents prior) ∧
    (state (.symbol .plus) 5 parameterEvents prior).diagnostics = prior ++ parameterEvents := by
  rcases optionalLambdaReturnType_concrete_trace_reject_complete
      (input := state (.symbol .plus) 4 parameterEvents prior) return_rejection with
    ⟨actual, rejected, result, afterEq, reportEq, events⟩
  cases Failure.toDiagnostic_injective reportEq
  have frame := optionalLambdaReturnType_reject_context result
  have same := State.eq_traceResult_of_fields frame.1 (congrArg TokenWindow.endByte frame.2) afterEq events
  rw [same] at result
  have returned : optionalLambdaReturnType (state (.symbol .plus) 4 parameterEvents prior) =
      .reject returnFailure (state (.symbol .plus) 5 parameterEvents prior) := by
    simpa only [State.traceResult, state, remainder, List.reverse_nil, List.nil_append] using result
  refine ⟨lambdaExpression_eq_reject_of_return (marker_result _ prior) (parameters_result _ prior)
    returned, ?_⟩
  simp only [state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem mixed_parameter_events_filter_before_return_and_body (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical parameter.span)
    {bodyEvents keptBody : List ParseDiagnostic}
    (bodyFiltered : ParseDiagnosticCascadeFilters text lexical bodyEvents keptBody) :
    ParseDiagnosticCascadeFilters text lexical (prefixEvents ++ bodyEvents) ([returnEvent] ++ keptBody) := by
  have parameterFiltered : ParseDiagnosticCascadeFilters text lexical parameterEvents [] :=
    .drop ⟨by trivial, suppressed⟩ (.drop ⟨by trivial, suppressed⟩ .nil)
  exact lambdaExpressionTrace_cascadeFilters return_trace text lexical parameterFiltered bodyFiltered

theorem mixed_parameter_events_filter_before_return_rejection (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical parameter.span) :
    ParseDiagnosticCascadeFilters text lexical parameterEvents [] := by
  have filtered := lambdaExpressionReturnRejectionTrace_cascadeFilters return_rejection text lexical
    (show ParseDiagnosticCascadeFilters text lexical parameterEvents [] from
      .drop ⟨by trivial, suppressed⟩ (.drop ⟨by trivial, suppressed⟩ .nil))
  simpa only [List.append_nil] using filtered

private def emptyBody : Block := { span := span 14 16, value := [] }

/-- Genuine empty Core block: neither a supplied statement nor body diagnostic
is executed, while the semicolon and all earlier diagnostics remain intact. -/
theorem typed_empty_body_preserves_suffix (statement : Parser Statement) (prior : List ParseDiagnostic) :
    lambdaExpression (coreBlock statement .allow) (state typedKind 0 [] prior) =
      .ok (lambdaExpressionTraceValue (span 0 3) parameters (some returnType) emptyBody)
        (state typedKind 8 prefixEvents prior) ∧
    (state typedKind 8 prefixEvents prior).diagnostics = prior ++ prefixEvents ∧
    (state typedKind 8 prefixEvents prior).peek? = some (token 16 17 (.symbol .semicolon)) := by
  have opening : symbol .leftBrace .statement (state typedKind 6 prefixEvents prior) =
      .ok (token 14 15 (.symbol .leftBrace)) (state typedKind 7 prefixEvents prior) :=
    symbol_eq_ok_of_exactTokenParses .leftBrace .statement ⟨⟨by change 6 < 9; decide, rfl⟩, rfl⟩
  have closing : symbol .rightBrace .statement (state typedKind 7 prefixEvents prior) =
      .ok (token 15 16 (.symbol .rightBrace)) (state typedKind 8 prefixEvents prior) :=
    symbol_eq_ok_of_exactTokenParses .rightBrace .statement ⟨⟨by change 7 < 9; decide, rfl⟩, rfl⟩
  have bodyResult : coreBlock statement .allow (state typedKind 6 prefixEvents prior) =
      .ok emptyBody (state typedKind 8 prefixEvents prior) := by
    simp only [coreBlock, opening, coreBlockItems, show isSymbol (state typedKind 7 prefixEvents prior) .rightBrace = true from rfl,
      ↓reduceIte, closeCoreBlock, bind, closing, modifyState, pure]
    rfl
  exact ⟨(typed_success_keeps_all_components prior emptyBody _ bodyResult).1,
    (typed_success_keeps_all_components prior emptyBody _ bodyResult).2.2, rfl⟩

end Solcore.Test.SyntaxLambdaExpressionTraceProperties
