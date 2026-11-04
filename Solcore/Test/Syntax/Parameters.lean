import Solcore.Syntax.Parser.LambdaExpressionSuccessTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionRejectionTraceStateProperties
import Solcore.Syntax.DeclarativeLambdaExpressionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeProperties
import Solcore.Syntax.Parser.CoreBlockClosingTraceProperties
import Solcore.Syntax.Parser.LambdaParameterRawTraceStateProperties
import Solcore.Syntax.Parser.ParameterDispatchTraceProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTraceExistenceProperties
import Solcore.Syntax.Parser.LambdaParameterTailTraceStateProperties
import Solcore.Syntax.DeclarativeLambdaParameterTraceProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTraceProperties
import Solcore.Syntax.Parser.LambdaParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.LambdaParameterTraceStateProperties
import Solcore.Syntax.Parser.NamedParameterRawTraceStateProperties
import Solcore.Syntax.Parser.NamedParameterCoreTraceExistenceProperties
import Solcore.Syntax.Parser.NamedParameterTailTraceStateProperties
import Solcore.Syntax.DeclarativeNamedParameterTraceProperties
import Solcore.Syntax.Parser.NamedParameterCoreTraceProperties
import Solcore.Syntax.Parser.ParameterRecoveryTraceProperties
import Solcore.Syntax.Parser.NamedParameterTraceStateProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceExactnessProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProtectionProperties
import Solcore.Syntax.Parser.OptionalLambdaReturnTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties
import Solcore.Syntax.Parser.FunctionParametersTraceProperties
import Solcore.Syntax.Parser.LambdaParametersTraceProperties
import Solcore.Syntax.Parser.ParameterNameFinishingTraceProperties
import Solcore.Syntax.Parser.LambdaParameterCoreTotalityProperties
import Solcore.Syntax.Parser.CoreLambdaParameterOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.LambdaParameterTotalityProperties
import Solcore.Syntax.Parser.NamedParameterTotalityProperties
import Solcore.Syntax.Parser.ParameterRecoveryTotalityProperties
import Solcore.Syntax.Parser.TypedParameterFinishingTraceProperties
import Solcore.Syntax.DeclarativeQualifiedNameTraceGrammar
import Solcore.Syntax.DeclarativeNamedTypeFinishingTraceGrammar

/-!
# Parameter syntax tests

Parameter lists: named, typed and lambda parameters, their raw, core and tail traces, recovery
and the lambda expression around them.
-/

section
-- leanmerge: from Solcore.Test.SyntaxLambdaExpressionTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterRawTraceProperties
/-! Independent raw parameter derivations reconstruct complete replies. These
are raw ordinary/comptime lambda paths, not public recovering parameter parsers.
The token fixtures intentionally require no source/window validity hypothesis. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterRawTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open LambdaParameterInternals

private def source : SourceId := { origin := .main, path := "raw-parameter-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def name (startByte endByte : Nat) (value : String) : Identifier := { span := span startByte endByte, value }
private def ident (n : Identifier) : Token := { span := n.span, value := .identifier n.value }
private def symbol (startByte endByte : Nat) (value : Symbol) : Token := { span := span startByte endByte, value := .symbol value }
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}
private def input (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor := 0
  window := { endIndex := tokens.length, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def final (tokens : List Token) (cursor : Nat) (events prior : List ParseDiagnostic) : State := {
  input tokens prior with cursor, diagnosticsRev := events.reverse ++ prior.reverse
}
private def hyphen (n : Identifier) : ParseDiagnostic := { span := n.span, kind := .invalidIdentifierHyphen n.value }
private def constraint (s : SourceSpan) (kind : ParseConstraint) : ParseDiagnostic := {
  span := s, kind := .constraintViolation kind
}

private theorem final_diagnostics (tokens : List Token) (cursor : Nat) (events prior : List ParseDiagnostic) :
    (final tokens cursor events prior).diagnostics = prior ++ events := by
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

private theorem leaf_trace {before after : Remainder} {n : Identifier} {events : List ParseDiagnostic}
    (head : IdentifierTraceParses before n after events)
    (noDot : TokenKindAbsentAt after.tokens after.endIndex after.cursor (.symbol .dot))
    (noArguments : TokenKindAbsentAt after.tokens after.endIndex after.cursor (.symbol .less))
    (ordinary : ¬ UnqualifiedMappingSpelling (tracedQualifiedName n []))
    (selection : TypeDispatchSelects before .named) :
    TypeExprTraceParses source 99 before (namedTypeTraceValue (tracedQualifiedName n []) none) after events := by
  have qualified : QualifiedNameTraceParses source 99 before (tracedQualifiedName n []) after events := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head (.done noDot)
  apply TypeExprTraceParses.roll
  apply TypeDispatchTraceParses.selected .named selection
  change NamedTypeTraceParses TypeExprTraceParses source 99 before
    (namedTypeTraceValue (tracedQualifiedName n []) none) after events
  simpa only [List.append_nil] using NamedTypeTraceParses.parsed qualified
    (NamedTypeArgumentsTraceParses.absent (elementTrace := TypeExprTraceParses) noArguments)
    (NamedTypeFinishingTrace.ordinary ordinary)

private def comptimeName : Identifier := name 0 8 "comptime"
private def bareTokens : List Token := [ident comptimeName, symbol 8 9 .semicolon]
private def nameWarning : ParseDiagnostic := constraint comptimeName.span .comptimeUsedAsParameterName
private def bareFailure : Failure := {
  span := span 8 9, found := some (.symbol .semicolon)
  expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem bare_ordinary_trace : OrdinaryLambdaParameterTraceParses source 99
    (remainder bareTokens 0) { span := comptimeName.span, value := .inferred comptimeName }
    (remainder bareTokens 1) [nameWarning] := by
  have head : IdentifierTraceParses (remainder bareTokens 0) comptimeName (remainder bareTokens 1) [] :=
    .parsed ⟨⟨by change 0 < 2; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling comptimeName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder bareTokens 0) comptimeName
      (remainder bareTokens 1) [nameWarning] :=
    .parsed head (.comptime rfl)
  simpa only [List.append_nil] using OrdinaryLambdaParameterTraceParses.parsed checked (.inferred
    (by simp [TokenKindAbsentAt, TokenAt, remainder, bareTokens, symbol]))

private theorem bare_comptime_trace : ComptimeLambdaParameterTraceRejects source 99
    (remainder bareTokens 0) (remainder bareTokens 1) bareFailure.toDiagnostic [] :=
  .nameRejected comptimeName.span ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩
    (by simp [IdentifierAbsentAt, TokenAt, remainder, bareTokens, symbol])
    (.reported (.token (current := symbol 8 9 .semicolon) ⟨by change 1 < 2; decide, rfl⟩))

/-- Reusable independent witnesses retain the distinction between raw paths. -/
theorem bare_comptime_raw_traces :
    OrdinaryLambdaParameterTraceParses source 99 (remainder bareTokens 0)
      { span := comptimeName.span, value := .inferred comptimeName } (remainder bareTokens 1) [nameWarning] ∧
    ComptimeLambdaParameterTraceRejects source 99 (remainder bareTokens 0)
      (remainder bareTokens 1) bareFailure.toDiagnostic [] ∧
    ComptimeParameterPrefixAbsentAt (remainder bareTokens 0) :=
  ⟨bare_ordinary_trace, bare_comptime_trace,
    ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input bareTokens []) = false from rfl)⟩

/-- The same `comptime;` carrier has different raw outcomes. Its selected core
chooses ordinary, since the second token is not an identifier. -/
theorem same_input_distinguishes_raw_paths (prior : List ParseDiagnostic) :
    ordinaryLambdaParameter (input bareTokens prior) = .ok { span := comptimeName.span, value := .inferred comptimeName }
      (final bareTokens 1 [nameWarning] prior) ∧
    comptimeLambdaParameter (input bareTokens prior) = .reject bareFailure (final bareTokens 1 [] prior) ∧
    (final bareTokens 1 [nameWarning] prior).diagnostics = prior ++ [nameWarning] ∧
    (final bareTokens 1 [] prior).diagnostics = prior ∧
    lambdaParameterCore (input bareTokens prior) = ordinaryLambdaParameter (input bareTokens prior) := by
  refine ⟨(ordinaryLambdaParameter_trace_success_state_iff (input := input bareTokens prior)).mp bare_ordinary_trace,
    (comptimeLambdaParameter_trace_reject_failure_state_iff (input := input bareTokens prior)).mp bare_comptime_trace,
    final_diagnostics _ _ _ _, ?_, ?_⟩
  · simpa only [List.append_nil] using final_diagnostics bareTokens 1 [] prior
  · exact lambdaParameterCore_eq_ordinary_of_prefix_absent
      (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
        ParameterDispatchTraceInternals.comptimeGuard (input bareTokens prior) = false from rfl))

private def ordinaryName : Identifier := name 0 3 "a-b"
private def typeName : Identifier := name 14 17 "c-d"
private def typedTokens : List Token := [ident ordinaryName, symbol 3 4 .colon,
  ident (name 5 13 "comptime"), symbol 13 14 .less, ident typeName,
  symbol 17 18 .greater, symbol 18 19 .semicolon]
private def leaf : TypeExpr := namedTypeTraceValue (tracedQualifiedName typeName []) none
private def outer : TypeExpr := comptimeTypeTraceValue (span 5 13) (span 13 14) (span 17 18) leaf
private def typedValue : LambdaParameter := lambdaParameterTraceValue (typedParameterTraceValue ordinaryName.span none ordinaryName outer)
private def typedEvents : List ParseDiagnostic :=
  [hyphen ordinaryName, hyphen typeName, constraint outer.span .comptimeTypeInParameter]

theorem typed_trace : OrdinaryLambdaParameterTraceParses source 99
    (remainder typedTokens 0) typedValue (remainder typedTokens 6) typedEvents := by
  have head : IdentifierTraceParses (remainder typedTokens 0) ordinaryName
      (remainder typedTokens 1) [hyphen ordinaryName] :=
    .parsed ⟨⟨by change 0 < 7; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling ordinaryName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder typedTokens 0) ordinaryName
      (remainder typedTokens 1) [hyphen ordinaryName] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
      (ParameterNameFinishingTrace.ordinary (by decide))
  have child : TypeExprTraceParses source 99 (remainder typedTokens 4) leaf
      (remainder typedTokens 5) [hyphen typeName] := by
    apply leaf_trace
    · exact .parsed ⟨⟨by change 4 < 7; decide, rfl⟩, rfl, rfl, rfl⟩
        (.hyphen (by unfold IdentifierHyphenSpelling typeName name; decide))
    · simp [TokenKindAbsentAt, TokenAt, remainder, typedTokens, symbol]
    · simp [TokenKindAbsentAt, TokenAt, remainder, typedTokens, symbol]
    · unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix typeName name; decide
    · exact TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input typedTokens [] with cursor := 4 } = .named from rfl)
  have typed : TypeExprTraceParses source 99 (remainder typedTokens 2) outer
      (remainder typedTokens 6) [hyphen typeName] :=
    TypeExprTraceParses.roll (.selected .comptime
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input typedTokens [] with cursor := 2 } = .comptime from rfl))
      (.parsed (span 5 13) (span 13 14) (span 17 18)
        ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩ ⟨⟨by change 3 < 7; decide, rfl⟩, rfl⟩
        child ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩))
  have tail : NamedParameterTailTraceParses ordinaryName.span none ordinaryName ordinaryName.span
      source 99 (remainder typedTokens 1) (typedParameterTraceValue ordinaryName.span none ordinaryName outer) (remainder typedTokens 6)
      [hyphen typeName, constraint outer.span .comptimeTypeInParameter] :=
    .typed (afterColon := remainder typedTokens 2) (type := outer)
      (span 3 4) ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩ typed
      (.comptime (by intro allowed; exact allowed))
  exact .parsed checked (.typed ⟨span 3 4, ⟨by change 1 < 7; decide, rfl⟩⟩ tail)

theorem typed_prefix_absent : ComptimeParameterPrefixAbsentAt (remainder typedTokens 0) :=
  ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
    ParameterDispatchTraceInternals.comptimeGuard (input typedTokens []) = false from rfl)

/-- Checked-name events precede nested type events, then the outer-comptime
parameter constraint. The complete AST and untouched semicolon are retained. -/
theorem name_type_finishing_order (prior : List ParseDiagnostic) :
    ordinaryLambdaParameter (input typedTokens prior) = .ok typedValue (final typedTokens 6 typedEvents prior) ∧
    (final typedTokens 6 typedEvents prior).diagnostics = prior ++ typedEvents ∧
    typedValue.span = span 0 18 ∧ outer.span = span 5 18 ∧
    outer.value = .comptime (span 5 13) (span 13 18) leaf ∧
    (final typedTokens 6 typedEvents prior).peek? = some (symbol 18 19 .semicolon) :=
  ⟨(ordinaryLambdaParameter_trace_success_state_iff (input := input typedTokens prior)).mp typed_trace,
    final_diagnostics _ _ _ _, rfl, rfl, rfl, rfl⟩

private def rejectTokens : List Token := [ident ordinaryName, symbol 3 4 .colon, symbol 4 5 .plus]
private def typeFailure : Failure := {
  span := span 4 5, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

theorem rejected_trace : OrdinaryLambdaParameterTraceRejects source 99
    (remainder rejectTokens 0) (remainder rejectTokens 2) typeFailure.toDiagnostic [hyphen ordinaryName] := by
  have head : IdentifierTraceParses (remainder rejectTokens 0) ordinaryName
      (remainder rejectTokens 1) [hyphen ordinaryName] :=
    .parsed ⟨⟨by change 0 < 3; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling ordinaryName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder rejectTokens 0) ordinaryName
      (remainder rejectTokens 1) [hyphen ordinaryName] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
      (ParameterNameFinishingTrace.ordinary (by decide))
  have rejected : TypeExprTraceRejects source 99 (remainder rejectTokens 2)
      (remainder rejectTokens 2) typeFailure.toDiagnostic [] :=
    TypeExprTraceRejects.roll (.selected .final
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input rejectTokens [] with cursor := 2 } = .final from rfl))
      (.rejected (.reported (.token (current := symbol 4 5 .plus) ⟨by change 2 < 3; decide, rfl⟩))))
  simpa only [List.append_nil] using OrdinaryLambdaParameterTraceRejects.tailRejected checked
    (.typeRejected (span 3 4) ⟨⟨by change 1 < 3; decide, rfl⟩, rfl⟩ rejected)

theorem reject_prefix_absent : ComptimeParameterPrefixAbsentAt (remainder rejectTokens 0) :=
  ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
    ParameterDispatchTraceInternals.comptimeGuard (input rejectTokens []) = false from rfl)

/-- A rejected type keeps the checked-name event but does not commit its
terminal report or execute parameter finishing. -/
theorem child_failure_preserves_name_events (prior : List ParseDiagnostic) :
    ordinaryLambdaParameter (input rejectTokens prior) =
      .reject typeFailure (final rejectTokens 2 [hyphen ordinaryName] prior) ∧
    (final rejectTokens 2 [hyphen ordinaryName] prior).diagnostics = prior ++ [hyphen ordinaryName] ∧
    (final rejectTokens 2 [hyphen ordinaryName] prior).peek? = some (symbol 4 5 .plus) :=
  ⟨(ordinaryLambdaParameter_trace_reject_failure_state_iff (input := input rejectTokens prior)).mp rejected_trace,
    final_diagnostics _ _ _ _, rfl⟩

private def secondName : Identifier := name 9 17 "comptime"
private def plainName : Identifier := name 19 20 "T"
private def markedTokens : List Token := [ident comptimeName, ident secondName,
  symbol 17 18 .colon, ident plainName, symbol 20 21 .semicolon]
private def plainType : TypeExpr := namedTypeTraceValue (tracedQualifiedName plainName []) none
private def markedValue : LambdaParameter :=
  lambdaParameterTraceValue (typedParameterTraceValue comptimeName.span (some comptimeName.span) secondName plainType)

theorem marked_trace : ComptimeLambdaParameterTraceParses source 99
    (remainder markedTokens 0) markedValue (remainder markedTokens 4) [] := by
  have checked : IdentifierTraceParses (remainder markedTokens 1) secondName (remainder markedTokens 2) [] :=
    .parsed ⟨⟨by change 1 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling secondName name; decide))
  have typed : TypeExprTraceParses source 99 (remainder markedTokens 3) plainType (remainder markedTokens 4) [] := by
    apply leaf_trace
    · exact .parsed ⟨⟨by change 3 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
        (.clean (by unfold IdentifierHyphenSpelling plainName name; decide))
    · simp [TokenKindAbsentAt, TokenAt, remainder, markedTokens, symbol]
    · simp [TokenKindAbsentAt, TokenAt, remainder, markedTokens, symbol]
    · unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix plainName name; decide
    · exact TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input markedTokens [] with cursor := 3 } = .named from rfl)
  have tail : NamedParameterTailTraceParses comptimeName.span (some comptimeName.span) secondName
      (SourceSpan.cover comptimeName.span secondName.span) source 99 (remainder markedTokens 2)
      (typedParameterTraceValue comptimeName.span (some comptimeName.span) secondName plainType) (remainder markedTokens 4) [] :=
    .typed (afterColon := remainder markedTokens 3) (type := plainType)
      (span 17 18) ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ typed (.ordinary trivial)
  exact .parsed (afterMarker := remainder markedTokens 1) comptimeName.span
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩ checked (.typed ⟨span 17 18, ⟨by change 2 < 5; decide, rfl⟩⟩ tail)

/-- A name spelling `comptime` after a marker is still checked, but does not
receive the ordinary-name constraint. The typed result has no new events. -/
theorem second_comptime_name_has_no_extra_warning (prior : List ParseDiagnostic) :
    comptimeLambdaParameter (input markedTokens prior) = .ok markedValue (final markedTokens 4 [] prior) ∧
    (final markedTokens 4 [] prior).diagnostics = prior ∧
    markedValue.span = span 0 20 ∧
    markedValue.value = .typed (some (span 0 8)) secondName plainType ∧
    (final markedTokens 4 [] prior).peek? = some (symbol 20 21 .semicolon) := by
  refine ⟨(comptimeLambdaParameter_trace_success_state_iff (input := input markedTokens prior)).mp marked_trace,
    ?_, rfl, rfl, rfl⟩
  simpa only [List.append_nil] using final_diagnostics markedTokens 4 [] prior

private def missingTokens : List Token := [ident comptimeName, ident secondName, symbol 17 18 .rightParen]
private def missingEvent : ParseDiagnostic := constraint (span 0 17) .comptimeParameterRequiresType
private def missingValue : LambdaParameter := { span := span 0 17, value := .error }

/-- A marked name without a type is not inferred. The sole new event covers
the marker and name; even a second `comptime` name adds no name warning. -/
theorem marked_missing_trace : ComptimeLambdaParameterTraceParses source 99
    (remainder missingTokens 0) missingValue (remainder missingTokens 2) [missingEvent] := by
  have checked : IdentifierTraceParses (remainder missingTokens 1) secondName (remainder missingTokens 2) [] :=
    .parsed ⟨⟨by change 1 < 3; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling secondName name; decide))
  exact .parsed (afterMarker := remainder missingTokens 1) comptimeName.span
    ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩ checked
    (.typeMissing (by simp [TokenKindAbsentAt, TokenAt, remainder, missingTokens, symbol]) .emitted)

theorem marked_missing_type_preserves_prior_and_right_paren (prior : List ParseDiagnostic) :
    comptimeLambdaParameter (input missingTokens prior) =
      .ok missingValue (final missingTokens 2 [missingEvent] prior) ∧
    (final missingTokens 2 [missingEvent] prior).diagnostics = prior ++ [missingEvent] ∧
    missingValue.span = span 0 17 ∧ missingEvent.span = missingValue.span ∧
    (final missingTokens 2 [missingEvent] prior).peek? = some (symbol 17 18 .rightParen) :=
  ⟨(comptimeLambdaParameter_trace_success_state_iff (input := input missingTokens prior)).mp marked_missing_trace,
    final_diagnostics _ _ _ _, rfl, rfl, rfl⟩

end Solcore.Test.SyntaxLambdaParameterRawTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterCoreTraceProperties
/-! Selected-core consumers reconstruct whole replies from independent raw
components. All input states and prior events are arbitrary; neither child
execution contracts nor diagnostic-free premises are needed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterCoreTraceProperties

open Syntax Syntax.Parser Syntax.Parser.LambdaParameterInternals
open Syntax.DeclarativeGrammar

private def stateFrom (source : SourceId) (endByte : Nat) (before : Remainder)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte }, diagnosticsRev := prior.reverse
}

private theorem restore_ordinary_priority
    {source : SourceId} {endByte : Nat} {before after rejected : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} {failure : Failure}
    (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (ordinary : OrdinaryLambdaParameterTraceParses source endByte before value after trace)
    (rawRejected : ComptimeLambdaParameterTraceRejects source endByte before rejected failure.toDiagnostic []) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) ∧
    comptimeLambdaParameter (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult rejected []) ∧
    ¬ ∃ rejected report events, LambdaParameterCoreTraceRejects source endByte before rejected report events := by
  have selected := LambdaParameterCoreTraceParses.ordinary absent ordinary
  refine ⟨lambdaParameterCore_trace_success_state_iff.mp selected,
    comptimeLambdaParameter_trace_reject_failure_state_iff.mp rawRejected, ?_⟩
  rintro ⟨_, _, _, rejection⟩
  exact rejection.disjoint_success ⟨_, _, _, selected⟩

/-- Reuse the independently constructed `comptime;` fixture. Its ordinary
inferred success wins; the raw comptime identifier failure is not a selected
failure. Existing events, including duplicate constraints, stay first. -/
theorem bare_comptime_selects_success_not_raw_early_failure (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder)
      (trace : List ParseDiagnostic) (failure : Failure) (rejected : Remainder),
      input.diagnostics = prior ∧
      lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
      comptimeLambdaParameter input = .reject failure (input.traceResult rejected []) ∧
      (¬ ∃ after report events, LambdaParameterCoreTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder after report events) ∧
      (∃ name, value.value = .inferred name ∧ name.value = "comptime") ∧
      trace.map (·.kind) = [.constraintViolation .comptimeUsedAsParameterName] ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = some (.symbol .semicolon) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult rejected []).diagnostics = prior ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have witnesses := SyntaxLambdaParameterRawTraceProperties.bare_comptime_raw_traces
  have replies := restore_ordinary_priority prior witnesses.2.2 witnesses.1 witnesses.2.1
  refine ⟨_, _, _, _, _, _, ?_, replies.1, replies.2.1, replies.2.2,
    ⟨_, rfl, rfl⟩, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

private theorem restore_ordinary_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (parsed : OrdinaryLambdaParameterTraceParses source endByte before value after trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_success_state_iff.mp (.ordinary absent parsed)

private theorem comptime_prefix_of_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : ComptimeLambdaParameterTraceParses source endByte before value after trace) :
    ComptimeLambdaParameterStartsAt before := by
  cases parsed with
  | parsed markerSpan marker checked _ =>
      rcases marker with ⟨token, rfl⟩
      exact ⟨markerSpan, _, _, token, (identifierTraceParses_iff.mp checked).1.1⟩

private theorem restore_comptime_success
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (parsed : ComptimeLambdaParameterTraceParses source endByte before value after trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_success_state_iff.mp (.comptime (comptime_prefix_of_success parsed) parsed)

/-- Reuse the raw nested-type witness: name checking, child checking, and the
outer-comptime finishing constraint stay in that order after pair selection. -/
theorem selected_nested_type_keeps_all_three_events (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder) (trace : List ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 18 ∧
      (∃ name type, value.value = .typed none name type ∧ name.value = "a-b" ∧ ¬ ParameterTypeAllowed type) ∧
      trace.map (·.kind) = [.invalidIdentifierHyphen "a-b", .invalidIdentifierHyphen "c-d",
        .constraintViolation .comptimeTypeInParameter] ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have result := restore_ordinary_success prior SyntaxLambdaParameterRawTraceProperties.typed_prefix_absent
    SyntaxLambdaParameterRawTraceProperties.typed_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, ⟨_, _, rfl, rfl, fun allowed => allowed⟩, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

/-- The selected second `comptime` name is typed without the ordinary-name
warning. A silent raw witness remains silent at the complete selected reply. -/
theorem selected_second_comptime_name_adds_no_warning (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after []) ∧
      (∃ marker name type, value.value = .typed (some marker) name type ∧ name.value = "comptime") ∧
      value.span.startByte = 0 ∧ value.span.endByte = 20 ∧
      (input.traceResult after []).diagnostics = prior ∧
      (input.traceResult after []).peek?.map (·.value) = some (.symbol .semicolon) := by
  have result := restore_comptime_success prior SyntaxLambdaParameterRawTraceProperties.marked_trace
  refine ⟨_, _, _, ?_, result, ⟨_, _, _, rfl, rfl⟩, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

/-- Pair selection keeps the marked missing-type error, not ordinary inference
or a name warning. Its event and error node have the same marker/name cover. -/
theorem selected_marked_missing_type_keeps_cover_error (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : LambdaParameter) (after : Remainder) (event : ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .ok value (input.traceResult after [event]) ∧
      value.value = .error ∧ value.span.startByte = 0 ∧ value.span.endByte = 17 ∧
      event.span = value.span ∧ event.kind = .constraintViolation .comptimeParameterRequiresType ∧
      (input.traceResult after [event]).diagnostics = prior ++ [event] ∧
      (input.traceResult after [event]).peek?.map (·.value) = some (.symbol .rightParen) := by
  have result := restore_comptime_success prior SyntaxLambdaParameterRawTraceProperties.marked_missing_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

private theorem restore_ordinary_rejection
    {source : SourceId} {endByte : Nat} {before after : Remainder}
    {failure : Failure} {trace : List ParseDiagnostic} (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (rejected : OrdinaryLambdaParameterTraceRejects source endByte before after failure.toDiagnostic trace) :
    lambdaParameterCore (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult after trace) :=
  lambdaParameterCore_trace_reject_failure_state_iff.mp (.ordinary absent rejected)

/-- A selected child rejection preserves the name event but does not emit its
terminal report or any finishing event. The complete Failure is retained. -/
theorem selected_child_failure_keeps_only_prior_and_name_event (prior : List ParseDiagnostic) :
    ∃ (input : State) (after : Remainder) (failure : Failure) (trace : List ParseDiagnostic),
      input.diagnostics = prior ∧ lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
      trace.map (·.kind) = [.invalidIdentifierHyphen "a-b"] ∧
      failure.expected = { head := .typeExpr, tail := [] } ∧ failure.context = .typeExpr ∧
      failure.found = some (.symbol .plus) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .plus) := by
  have result := restore_ordinary_rejection prior SyntaxLambdaParameterRawTraceProperties.reject_prefix_absent
    SyntaxLambdaParameterRawTraceProperties.rejected_trace
  refine ⟨_, _, _, _, ?_, result, rfl, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]

/-- Ordinary execution supplies existence, independently of joint uniqueness.
Every arbitrary State has a protected exact suffix and a reconstructed reply. -/
theorem every_state_has_a_protected_exact_core_reply (input : State) (lexical : List SourceSpan) :
    ∃ trace, ParseDiagnosticCascadeFilters input.file.content lexical trace trace ∧
      ((∃ value after,
        lambdaParameterCore input = .ok value (input.traceResult after trace) ∧
        LambdaParameterCoreTraceParses input.file.id input.window.endByte
          input.declarativeRemainder value after trace) ∨
       (∃ failure after,
        lambdaParameterCore input = .reject failure (input.traceResult after trace) ∧
        LambdaParameterCoreTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder after failure.toDiagnostic trace)) := by
  rcases lambdaParameterCore_exists_trace_outcome input with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact ⟨trace, parsed.cascadeFilters _ _, .inl
      ⟨value, output.declarativeRemainder, lambdaParameterCore_trace_success_state_iff.mp parsed, parsed⟩⟩
  · exact ⟨trace, rejection.cascadeFilters _ _, .inr
      ⟨failure, rejected.declarativeRemainder, lambdaParameterCore_trace_reject_failure_state_iff.mp rejection, rejection⟩⟩

end Solcore.Test.SyntaxLambdaParameterCoreTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterTailTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedParameterRawTraceProperties
/-! Independent raw parameter derivations reconstruct complete replies. These
are raw ordinary/comptime paths, not public recovering parameter parsers.
The token fixtures intentionally require no source/window validity hypothesis. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedParameterRawTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "raw-parameter-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def name (startByte endByte : Nat) (value : String) : Identifier := { span := span startByte endByte, value }
private def ident (n : Identifier) : Token := { span := n.span, value := .identifier n.value }
private def symbol (startByte endByte : Nat) (value : Symbol) : Token := { span := span startByte endByte, value := .symbol value }
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}
private def input (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor := 0
  window := { endIndex := tokens.length, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def final (tokens : List Token) (cursor : Nat) (events prior : List ParseDiagnostic) : State := {
  input tokens prior with cursor, diagnosticsRev := events.reverse ++ prior.reverse
}
private def hyphen (n : Identifier) : ParseDiagnostic := { span := n.span, kind := .invalidIdentifierHyphen n.value }
private def constraint (s : SourceSpan) (kind : ParseConstraint) : ParseDiagnostic := {
  span := s, kind := .constraintViolation kind
}

private theorem final_diagnostics (tokens : List Token) (cursor : Nat) (events prior : List ParseDiagnostic) :
    (final tokens cursor events prior).diagnostics = prior ++ events := by
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

private theorem leaf_trace {before after : Remainder} {n : Identifier} {events : List ParseDiagnostic}
    (head : IdentifierTraceParses before n after events)
    (noDot : TokenKindAbsentAt after.tokens after.endIndex after.cursor (.symbol .dot))
    (noArguments : TokenKindAbsentAt after.tokens after.endIndex after.cursor (.symbol .less))
    (ordinary : ¬ UnqualifiedMappingSpelling (tracedQualifiedName n []))
    (selection : TypeDispatchSelects before .named) :
    TypeExprTraceParses source 99 before (namedTypeTraceValue (tracedQualifiedName n []) none) after events := by
  have qualified : QualifiedNameTraceParses source 99 before (tracedQualifiedName n []) after events := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head (.done noDot)
  apply TypeExprTraceParses.roll
  apply TypeDispatchTraceParses.selected .named selection
  change NamedTypeTraceParses TypeExprTraceParses source 99 before
    (namedTypeTraceValue (tracedQualifiedName n []) none) after events
  simpa only [List.append_nil] using NamedTypeTraceParses.parsed qualified
    (NamedTypeArgumentsTraceParses.absent (elementTrace := TypeExprTraceParses) noArguments)
    (NamedTypeFinishingTrace.ordinary ordinary)

private def comptimeName : Identifier := name 0 8 "comptime"
private def bareTokens : List Token := [ident comptimeName, symbol 8 9 .semicolon]
private def nameWarning : ParseDiagnostic := constraint comptimeName.span .comptimeUsedAsParameterName
private def missingType : ParseDiagnostic := constraint comptimeName.span .namedParameterRequiresType
private def bareFailure : Failure := {
  span := span 8 9, found := some (.symbol .semicolon)
  expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem bare_ordinary_trace : OrdinaryNamedParameterTraceParses source 99
    (remainder bareTokens 0) (errorParameterTraceValue comptimeName.span)
    (remainder bareTokens 1) [nameWarning, missingType] := by
  have head : IdentifierTraceParses (remainder bareTokens 0) comptimeName (remainder bareTokens 1) [] :=
    .parsed ⟨⟨by change 0 < 2; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling comptimeName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder bareTokens 0) comptimeName
      (remainder bareTokens 1) [nameWarning] :=
    .parsed head (.comptime rfl)
  exact .parsed checked (.typeMissing
    (by simp [TokenKindAbsentAt, TokenAt, remainder, bareTokens, symbol]) .emitted)

private theorem bare_comptime_trace : ComptimeNamedParameterTraceRejects source 99
    (remainder bareTokens 0) (remainder bareTokens 1) bareFailure.toDiagnostic [] :=
  .nameRejected comptimeName.span ⟨⟨by change 0 < 2; decide, rfl⟩, rfl⟩
    (by simp [IdentifierAbsentAt, TokenAt, remainder, bareTokens, symbol])
    (.reported (.token (current := symbol 8 9 .semicolon) ⟨by change 1 < 2; decide, rfl⟩))

/-- Reusable independent witnesses retain the distinction between raw paths. -/
theorem bare_comptime_raw_traces :
    OrdinaryNamedParameterTraceParses source 99 (remainder bareTokens 0)
      (errorParameterTraceValue comptimeName.span) (remainder bareTokens 1) [nameWarning, missingType] ∧
    ComptimeNamedParameterTraceRejects source 99 (remainder bareTokens 0)
      (remainder bareTokens 1) bareFailure.toDiagnostic [] ∧
    ComptimeParameterPrefixAbsentAt (remainder bareTokens 0) :=
  ⟨bare_ordinary_trace, bare_comptime_trace,
    ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input bareTokens []) = false from rfl)⟩

/-- The same `comptime;` carrier has different raw outcomes. Its selected core
chooses ordinary, since the second token is not an identifier. -/
theorem same_input_distinguishes_raw_paths (prior : List ParseDiagnostic) :
    ordinaryNamedParameter (input bareTokens prior) = .ok (errorParameterTraceValue comptimeName.span)
      (final bareTokens 1 [nameWarning, missingType] prior) ∧
    comptimeNamedParameter (input bareTokens prior) = .reject bareFailure (final bareTokens 1 [] prior) ∧
    (final bareTokens 1 [nameWarning, missingType] prior).diagnostics = prior ++ [nameWarning, missingType] ∧
    (final bareTokens 1 [] prior).diagnostics = prior ∧
    namedParameterCore (input bareTokens prior) = ordinaryNamedParameter (input bareTokens prior) := by
  refine ⟨(ordinaryNamedParameter_trace_success_state_iff (input := input bareTokens prior)).mp bare_ordinary_trace,
    (comptimeNamedParameter_trace_reject_failure_state_iff (input := input bareTokens prior)).mp bare_comptime_trace,
    final_diagnostics _ _ _ _, ?_, ?_⟩
  · simpa only [List.append_nil] using final_diagnostics bareTokens 1 [] prior
  · exact namedParameterCore_eq_ordinary_of_prefix_absent
      (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
        ParameterDispatchTraceInternals.comptimeGuard (input bareTokens prior) = false from rfl))

private def ordinaryName : Identifier := name 0 3 "a-b"
private def typeName : Identifier := name 14 17 "c-d"
private def typedTokens : List Token := [ident ordinaryName, symbol 3 4 .colon,
  ident (name 5 13 "comptime"), symbol 13 14 .less, ident typeName,
  symbol 17 18 .greater, symbol 18 19 .semicolon]
private def leaf : TypeExpr := namedTypeTraceValue (tracedQualifiedName typeName []) none
private def outer : TypeExpr := comptimeTypeTraceValue (span 5 13) (span 13 14) (span 17 18) leaf
private def typedValue : FunctionParameter := typedParameterTraceValue ordinaryName.span none ordinaryName outer
private def typedEvents : List ParseDiagnostic :=
  [hyphen ordinaryName, hyphen typeName, constraint outer.span .comptimeTypeInParameter]

private theorem typed_trace : OrdinaryNamedParameterTraceParses source 99
    (remainder typedTokens 0) typedValue (remainder typedTokens 6) typedEvents := by
  have head : IdentifierTraceParses (remainder typedTokens 0) ordinaryName
      (remainder typedTokens 1) [hyphen ordinaryName] :=
    .parsed ⟨⟨by change 0 < 7; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling ordinaryName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder typedTokens 0) ordinaryName
      (remainder typedTokens 1) [hyphen ordinaryName] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
      (ParameterNameFinishingTrace.ordinary (by decide))
  have child : TypeExprTraceParses source 99 (remainder typedTokens 4) leaf
      (remainder typedTokens 5) [hyphen typeName] := by
    apply leaf_trace
    · exact .parsed ⟨⟨by change 4 < 7; decide, rfl⟩, rfl, rfl, rfl⟩
        (.hyphen (by unfold IdentifierHyphenSpelling typeName name; decide))
    · simp [TokenKindAbsentAt, TokenAt, remainder, typedTokens, symbol]
    · simp [TokenKindAbsentAt, TokenAt, remainder, typedTokens, symbol]
    · unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix typeName name; decide
    · exact TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input typedTokens [] with cursor := 4 } = .named from rfl)
  have typed : TypeExprTraceParses source 99 (remainder typedTokens 2) outer
      (remainder typedTokens 6) [hyphen typeName] :=
    TypeExprTraceParses.roll (.selected .comptime
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input typedTokens [] with cursor := 2 } = .comptime from rfl))
      (.parsed (span 5 13) (span 13 14) (span 17 18)
        ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩ ⟨⟨by change 3 < 7; decide, rfl⟩, rfl⟩
        child ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩))
  have tail : NamedParameterTailTraceParses ordinaryName.span none ordinaryName ordinaryName.span
      source 99 (remainder typedTokens 1) typedValue (remainder typedTokens 6)
      [hyphen typeName, constraint outer.span .comptimeTypeInParameter] :=
    .typed (afterColon := remainder typedTokens 2) (type := outer)
      (span 3 4) ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩ typed
      (.comptime (by intro allowed; exact allowed))
  exact .parsed checked tail

/-- Checked-name events precede nested type events, then the outer-comptime
parameter constraint. The complete AST and untouched semicolon are retained. -/
theorem name_type_finishing_order (prior : List ParseDiagnostic) :
    ordinaryNamedParameter (input typedTokens prior) = .ok typedValue (final typedTokens 6 typedEvents prior) ∧
    (final typedTokens 6 typedEvents prior).diagnostics = prior ++ typedEvents ∧
    typedValue.span = span 0 18 ∧ outer.span = span 5 18 ∧
    outer.value = .comptime (span 5 13) (span 13 18) leaf ∧
    (final typedTokens 6 typedEvents prior).peek? = some (symbol 18 19 .semicolon) :=
  ⟨(ordinaryNamedParameter_trace_success_state_iff (input := input typedTokens prior)).mp typed_trace,
    final_diagnostics _ _ _ _, rfl, rfl, rfl, rfl⟩

private def rejectTokens : List Token := [ident ordinaryName, symbol 3 4 .colon, symbol 4 5 .plus]
private def typeFailure : Failure := {
  span := span 4 5, found := some (.symbol .plus)
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

private theorem rejected_trace : OrdinaryNamedParameterTraceRejects source 99
    (remainder rejectTokens 0) (remainder rejectTokens 2) typeFailure.toDiagnostic [hyphen ordinaryName] := by
  have head : IdentifierTraceParses (remainder rejectTokens 0) ordinaryName
      (remainder rejectTokens 1) [hyphen ordinaryName] :=
    .parsed ⟨⟨by change 0 < 3; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling ordinaryName name; decide))
  have checked : CheckedParameterNameTraceParses (remainder rejectTokens 0) ordinaryName
      (remainder rejectTokens 1) [hyphen ordinaryName] := by
    simpa only [List.append_nil] using CheckedParameterNameTraceParses.parsed head
      (ParameterNameFinishingTrace.ordinary (by decide))
  have rejected : TypeExprTraceRejects source 99 (remainder rejectTokens 2)
      (remainder rejectTokens 2) typeFailure.toDiagnostic [] :=
    TypeExprTraceRejects.roll (.selected .final
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input rejectTokens [] with cursor := 2 } = .final from rfl))
      (.rejected (.reported (.token (current := symbol 4 5 .plus) ⟨by change 2 < 3; decide, rfl⟩))))
  simpa only [List.append_nil] using OrdinaryNamedParameterTraceRejects.tailRejected checked
    (.typeRejected (span 3 4) ⟨⟨by change 1 < 3; decide, rfl⟩, rfl⟩ rejected)

/-- A rejected type keeps the checked-name event but does not commit its
terminal report or execute parameter finishing. -/
theorem child_failure_preserves_name_events (prior : List ParseDiagnostic) :
    ordinaryNamedParameter (input rejectTokens prior) =
      .reject typeFailure (final rejectTokens 2 [hyphen ordinaryName] prior) ∧
    (final rejectTokens 2 [hyphen ordinaryName] prior).diagnostics = prior ++ [hyphen ordinaryName] ∧
    (final rejectTokens 2 [hyphen ordinaryName] prior).peek? = some (symbol 4 5 .plus) :=
  ⟨(ordinaryNamedParameter_trace_reject_failure_state_iff (input := input rejectTokens prior)).mp rejected_trace,
    final_diagnostics _ _ _ _, rfl⟩

private def secondName : Identifier := name 9 17 "comptime"
private def plainName : Identifier := name 19 20 "T"
private def markedTokens : List Token := [ident comptimeName, ident secondName,
  symbol 17 18 .colon, ident plainName, symbol 20 21 .semicolon]
private def plainType : TypeExpr := namedTypeTraceValue (tracedQualifiedName plainName []) none
private def markedValue : FunctionParameter :=
  typedParameterTraceValue comptimeName.span (some comptimeName.span) secondName plainType

private theorem marked_trace : ComptimeNamedParameterTraceParses source 99
    (remainder markedTokens 0) markedValue (remainder markedTokens 4) [] := by
  have checked : IdentifierTraceParses (remainder markedTokens 1) secondName (remainder markedTokens 2) [] :=
    .parsed ⟨⟨by change 1 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
      (.clean (by unfold IdentifierHyphenSpelling secondName name; decide))
  have typed : TypeExprTraceParses source 99 (remainder markedTokens 3) plainType (remainder markedTokens 4) [] := by
    apply leaf_trace
    · exact .parsed ⟨⟨by change 3 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
        (.clean (by unfold IdentifierHyphenSpelling plainName name; decide))
    · simp [TokenKindAbsentAt, TokenAt, remainder, markedTokens, symbol]
    · simp [TokenKindAbsentAt, TokenAt, remainder, markedTokens, symbol]
    · unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix plainName name; decide
    · exact TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch { input markedTokens [] with cursor := 3 } = .named from rfl)
  have tail : NamedParameterTailTraceParses comptimeName.span (some comptimeName.span) secondName
      (SourceSpan.cover comptimeName.span secondName.span) source 99 (remainder markedTokens 2)
      markedValue (remainder markedTokens 4) [] :=
    .typed (afterColon := remainder markedTokens 3) (type := plainType)
      (span 17 18) ⟨⟨by change 2 < 5; decide, rfl⟩, rfl⟩ typed (.ordinary trivial)
  exact .parsed (afterMarker := remainder markedTokens 1) comptimeName.span
    ⟨⟨by change 0 < 5; decide, rfl⟩, rfl⟩ checked tail

/-- A name spelling `comptime` after a marker is still checked, but does not
receive the ordinary-name constraint. The typed result has no new events. -/
theorem second_comptime_name_has_no_extra_warning (prior : List ParseDiagnostic) :
    comptimeNamedParameter (input markedTokens prior) = .ok markedValue (final markedTokens 4 [] prior) ∧
    (final markedTokens 4 [] prior).diagnostics = prior ∧
    markedValue.span = span 0 20 ∧
    markedValue.value = .typed (some (span 0 8)) secondName plainType ∧
    (final markedTokens 4 [] prior).peek? = some (symbol 20 21 .semicolon) := by
  refine ⟨(comptimeNamedParameter_trace_success_state_iff (input := input markedTokens prior)).mp marked_trace,
    ?_, rfl, rfl, rfl⟩
  simpa only [List.append_nil] using final_diagnostics markedTokens 4 [] prior

end Solcore.Test.SyntaxNamedParameterRawTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedParameterCoreTraceProperties
/-! Selected-core consumers reconstruct whole replies from independent raw
components. All input states and prior events are arbitrary; neither child
execution contracts nor diagnostic-free premises are needed. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedParameterCoreTraceProperties

open Syntax Syntax.Parser Syntax.Parser.FunctionParameterInternals
open Syntax.DeclarativeGrammar

private def stateFrom (source : SourceId) (endByte : Nat) (before : Remainder)
    (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := before.tokens, cursor := before.cursor
  window := { endIndex := before.endIndex, endByte }, diagnosticsRev := prior.reverse
}

private theorem restore_ordinary_priority
    {source : SourceId} {endByte : Nat} {before after rejected : Remainder}
    {value : FunctionParameter} {trace : List ParseDiagnostic} {failure : Failure}
    (prior : List ParseDiagnostic)
    (absent : ComptimeParameterPrefixAbsentAt before)
    (ordinary : OrdinaryNamedParameterTraceParses source endByte before value after trace)
    (rawRejected : ComptimeNamedParameterTraceRejects source endByte before rejected failure.toDiagnostic []) :
    namedParameterCore (stateFrom source endByte before prior) =
      .ok value ((stateFrom source endByte before prior).traceResult after trace) ∧
    comptimeNamedParameter (stateFrom source endByte before prior) =
      .reject failure ((stateFrom source endByte before prior).traceResult rejected []) ∧
    ¬ ∃ rejected report events, NamedParameterCoreTraceRejects source endByte before rejected report events := by
  have selected := NamedParameterCoreTraceParses.ordinary absent ordinary
  refine ⟨namedParameterCore_trace_success_state_iff.mp selected,
    comptimeNamedParameter_trace_reject_failure_state_iff.mp rawRejected, ?_⟩
  rintro ⟨_, _, _, rejection⟩
  exact rejection.disjoint_success ⟨_, _, _, selected⟩

/-- Reuse the independently constructed `comptime;` fixture. Its ordinary
error-valued success wins; the raw comptime identifier failure is not a selected
failure. Existing events, including duplicates of either constraint, stay first. -/
theorem bare_comptime_selects_success_not_raw_early_failure (prior : List ParseDiagnostic) :
    ∃ (input : State) (value : FunctionParameter) (after : Remainder)
      (trace : List ParseDiagnostic) (failure : Failure) (rejected : Remainder),
      input.diagnostics = prior ∧
      namedParameterCore input = .ok value (input.traceResult after trace) ∧
      comptimeNamedParameter input = .reject failure (input.traceResult rejected []) ∧
      (¬ ∃ after report events, NamedParameterCoreTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder after report events) ∧
      value.value = .error ∧
      trace.map (·.kind) = [.constraintViolation .comptimeUsedAsParameterName,
        .constraintViolation .namedParameterRequiresType] ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = some (.symbol .semicolon) ∧
      (input.traceResult after trace).diagnostics = prior ++ trace ∧
      (input.traceResult rejected []).diagnostics = prior ∧
      (input.traceResult after trace).peek?.map (·.value) = some (.symbol .semicolon) := by
  have witnesses := SyntaxNamedParameterRawTraceProperties.bare_comptime_raw_traces
  have replies := restore_ordinary_priority prior witnesses.2.2 witnesses.1 witnesses.2.1
  refine ⟨_, _, _, _, _, _, ?_, replies.1, replies.2.1, replies.2.2,
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse]
  · rw [State.traceResult_diagnostics]
    simp only [stateFrom, State.diagnostics, List.reverse_reverse, List.append_nil]

/-- Checked-name events precede type events, which precede finishing events.
The exact covering AST and every remainder field are restored together. -/
theorem ordinary_typed_components_restore_selected_reply
    {input : State} {afterName afterColon output : Remainder}
    {name : Identifier} {type : TypeExpr} {colonSpan : SourceSpan}
    {nameEvents typeEvents finishingEvents : List ParseDiagnostic}
    (absent : ComptimeParameterPrefixAbsentAt input.declarativeRemainder)
    (nameParsed : CheckedParameterNameTraceParses input.declarativeRemainder name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeParsed : TypeExprTraceParses input.file.id input.window.endByte afterColon type output typeEvents)
    (finished : TypedParameterFinishingTrace type finishingEvents) :
    namedParameterCore input = .ok (typedParameterTraceValue name.span none name type)
      (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)) ∧
    (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)).diagnostics =
      input.diagnostics ++ nameEvents ++ typeEvents ++ finishingEvents := by
  constructor
  · apply namedParameterCore_trace_success_state_iff.mp
    simpa only [List.append_assoc] using NamedParameterCoreTraceParses.ordinary absent
      (OrdinaryNamedParameterTraceParses.parsed nameParsed
        (.typed colonSpan colon typeParsed finished))
  · simp only [State.traceResult_diagnostics, List.append_assoc]

/-- A selected marker is silent. Even when the following name spells
`comptime`, only its identifier trace is used, without ordinary-name finishing. -/
theorem comptime_typed_components_restore_selected_reply
    {input : State} {afterMarker afterName afterColon output : Remainder}
    {markerSpan colonSpan : SourceSpan} {name : Identifier} {type : TypeExpr}
    {nameEvents typeEvents finishingEvents : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder)
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling)
      input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeParsed : TypeExprTraceParses input.file.id input.window.endByte afterColon type output typeEvents)
    (finished : TypedParameterFinishingTrace type finishingEvents) :
    namedParameterCore input = .ok (typedParameterTraceValue markerSpan (some markerSpan) name type)
      (input.traceResult output (nameEvents ++ typeEvents ++ finishingEvents)) := by
  apply namedParameterCore_trace_success_state_iff.mp
  simpa only [List.append_assoc] using NamedParameterCoreTraceParses.comptime present
    (ComptimeNamedParameterTraceParses.parsed markerSpan marker nameParsed
      (.typed colonSpan colon typeParsed finished))

/-- A failed type contributes its complete Failure and its own trace only:
no typed-parameter finishing event or committed terminal report is added. -/
theorem comptime_type_rejection_restores_selected_full_failure
    {input : State} {afterMarker afterName afterColon rejected : Remainder}
    {markerSpan colonSpan : SourceSpan} {name : Identifier} {failure : Failure}
    {nameEvents typeEvents : List ParseDiagnostic}
    (present : ComptimeLambdaParameterStartsAt input.declarativeRemainder)
    (marker : ExactTokenParses (.identifier ContextualKeyword.comptime.spelling)
      input.declarativeRemainder markerSpan afterMarker)
    (nameParsed : IdentifierTraceParses afterMarker name afterName nameEvents)
    (colon : ExactTokenParses (.symbol .colon) afterName colonSpan afterColon)
    (typeRejected : TypeExprTraceRejects input.file.id input.window.endByte afterColon
      rejected failure.toDiagnostic typeEvents) :
    namedParameterCore input = .reject failure (input.traceResult rejected (nameEvents ++ typeEvents)) ∧
    (input.traceResult rejected (nameEvents ++ typeEvents)).diagnostics =
      input.diagnostics ++ nameEvents ++ typeEvents := by
  constructor
  · exact namedParameterCore_trace_reject_failure_state_iff.mp (.comptime present
      (.tailRejected markerSpan marker nameParsed (.typeRejected colonSpan colon typeRejected)))
  · simp only [State.traceResult_diagnostics, List.append_assoc]

/-- Ordinary execution supplies existence, independently of joint uniqueness.
Every arbitrary State has a protected exact suffix and a reconstructed reply. -/
theorem every_state_has_a_protected_exact_core_reply (input : State) (lexical : List SourceSpan) :
    ∃ trace, ParseDiagnosticCascadeFilters input.file.content lexical trace trace ∧
      ((∃ value after,
        namedParameterCore input = .ok value (input.traceResult after trace) ∧
        NamedParameterCoreTraceParses input.file.id input.window.endByte
          input.declarativeRemainder value after trace) ∨
       (∃ failure after,
        namedParameterCore input = .reject failure (input.traceResult after trace) ∧
        NamedParameterCoreTraceRejects input.file.id input.window.endByte
          input.declarativeRemainder after failure.toDiagnostic trace)) := by
  rcases namedParameterCore_exists_trace_outcome input with
    ⟨value, output, trace, _, parsed, _⟩ | ⟨failure, rejected, trace, _, rejection, _⟩
  · exact ⟨trace, parsed.cascadeFilters _ _, .inl
      ⟨value, output.declarativeRemainder, namedParameterCore_trace_success_state_iff.mp parsed, parsed⟩⟩
  · exact ⟨trace, rejection.cascadeFilters _ _, .inr
      ⟨failure, rejected.declarativeRemainder, namedParameterCore_trace_reject_failure_state_iff.mp rejection, rejection⟩⟩

end Solcore.Test.SyntaxNamedParameterCoreTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedParameterTailTraceProperties
/-! Independent tail derivations reconstruct actual execution through the
whole-state correspondences. Type events precede parameter-finishing events;
missing colons succeed with an error value, and failed dotted type names keep
only their checked-name event and an uncommitted identifier report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedParameterTailTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "named-parameter-tail.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def sym (first last : Nat) (symbol : Symbol) : Token := { span := span first last, value := .symbol symbol }
private def name : Identifier := { span := span 0 3, value := "arg" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}
private def state (content : String) (tokens : List Token) (endByte : Nat)
    (prior : List ParseDiagnostic) (cursor : Nat) (fresh : List ParseDiagnostic) : State := {
  file := { id := source, content }, tokens := tokens.toArray, cursor
  window := { endIndex := tokens.length, endByte }, diagnosticsRev := fresh.reverse ++ prior.reverse
}

private def successName : Identifier := { span := span 13 16, value := "a-b" }
private def successNameToken : Token := { span := successName.span, value := .identifier successName.value }
private def successTokens : List Token := [nameToken, sym 3 4 .colon,
  { span := span 4 12, value := .identifier "comptime" }, sym 12 13 .less,
  successNameToken, sym 16 17 .greater, sym 17 18 .semicolon]
private def inner : TypeExpr := namedTypeTraceValue (tracedQualifiedName successName []) none
private def type : TypeExpr := comptimeTypeTraceValue (span 4 12) (span 12 13) (span 16 17) inner
private def parameter : FunctionParameter := { span := span 0 17, value := .typed none name type }
private def typeEvent : ParseDiagnostic := {
  span := successName.span, kind := .invalidIdentifierHyphen successName.value
}
private def finishingEvent : ParseDiagnostic := {
  span := span 4 17, kind := .constraintViolation .comptimeTypeInParameter
}
private def successState := state "arg:comptime<a-b>;" successTokens 18

private theorem success_trace :
    NamedParameterTailTraceParses name.span none name name.span source 18
      (remainder successTokens 1) parameter (remainder successTokens 6) [typeEvent, finishingEvent] := by
  let r := remainder successTokens
  have head : IdentifierTraceParses (r 4) successName (r 5) [typeEvent] :=
    .parsed ⟨⟨by change 4 < 7; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling successName; decide))
  have qualified : QualifiedNameTraceParses source 18 (r 4) (tracedQualifiedName successName []) (r 5) [typeEvent] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head
      (DottedIdentifierTailTraceParses.done
        (by simp [TokenKindAbsentAt, TokenAt, r, remainder, successTokens, sym]))
  have named : NamedTypeTraceParses TypeExprTraceParses source 18 (r 4) inner (r 5) [typeEvent] := by
    simpa only [List.append_nil, inner] using NamedTypeTraceParses.parsed qualified
      (NamedTypeArgumentsTraceParses.absent
        (by simp [TokenKindAbsentAt, TokenAt, r, remainder, successTokens, sym]))
      (NamedTypeFinishingTrace.ordinary (by
        unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix successName
        decide))
  have nested : TypeExprTraceParses source 18 (r 4) inner (r 5) [typeEvent] :=
    TypeExprTraceParses.roll (.selected .named
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (successState [] 4 []) = .named from rfl)) named)
  have comptime : ComptimeTypeTraceParses TypeExprTraceParses source 18 (r 2) type (r 6) [typeEvent] :=
    .parsed (span 4 12) (span 12 13) (span 16 17)
      ⟨⟨by change 2 < 7; decide, rfl⟩, rfl⟩
      ⟨⟨by change 3 < 7; decide, rfl⟩, rfl⟩ nested
      ⟨⟨by change 5 < 7; decide, rfl⟩, rfl⟩
  have typed : TypeExprTraceParses source 18 (r 2) type (r 6) [typeEvent] :=
    TypeExprTraceParses.roll (.selected .comptime
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (successState [] 2 []) = .comptime from rfl)) comptime)
  have finished : TypedParameterFinishingTrace type [finishingEvent] :=
    .comptime (by simp [ParameterTypeAllowed, type, comptimeTypeTraceValue])
  exact NamedParameterTailTraceParses.typed (input := r 1) (span 3 4)
    ⟨⟨by change 1 < 7; decide, rfl⟩, rfl⟩ typed finished

theorem comptime_tail_reconstructed (prior : List ParseDiagnostic) :
    NamedParameterTailTraceParses name.span none name name.span source 18
      (remainder successTokens 1) parameter (remainder successTokens 6) [typeEvent, finishingEvent] ∧
      namedParameterTail name.span none name name.span (successState prior 1 []) =
        .ok parameter (successState prior 6 [typeEvent, finishingEvent]) ∧
      (successState prior 6 [typeEvent, finishingEvent]).diagnostics = prior ++ [typeEvent, finishingEvent] ∧
      (successState prior 6 [typeEvent, finishingEvent]).peek? = some (sym 17 18 .semicolon) ∧
      (successState prior 6 [typeEvent, finishingEvent]).window = { endIndex := 7, endByte := 18 } := by
  refine ⟨success_trace, ?_, ?_, rfl, rfl⟩
  · exact (namedParameterTail_trace_success_state_iff name.span none name name.span
      (input := successState prior 1 [])).mp success_trace
  · simp only [successState, state, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem repeated_finishing_event_is_not_collapsed (prior : List ParseDiagnostic) :
    namedParameterTail name.span none name name.span
        (successState (prior ++ [finishingEvent, finishingEvent]) 1 []) =
      .ok parameter (successState (prior ++ [finishingEvent, finishingEvent]) 6 [typeEvent, finishingEvent]) ∧
      (successState (prior ++ [finishingEvent, finishingEvent]) 6 [typeEvent, finishingEvent]).diagnostics =
        prior ++ [finishingEvent, finishingEvent, typeEvent, finishingEvent] := by
  have result := comptime_tail_reconstructed (prior ++ [finishingEvent, finishingEvent])
  exact ⟨result.2.1, by
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.2.1⟩

private def missingTokens : List Token := [nameToken, sym 3 4 .semicolon]
private def missingEvent : ParseDiagnostic := {
  span := name.span, kind := .constraintViolation .namedParameterRequiresType
}
private def missingState := state "arg;" missingTokens 4

theorem missing_colon_is_error_success (prior : List ParseDiagnostic) :
    NamedParameterTailTraceParses name.span none name name.span source 4
      (remainder missingTokens 1) (errorParameterTraceValue name.span) (remainder missingTokens 1) [missingEvent] ∧
      namedParameterTail name.span none name name.span (missingState prior 1 []) =
        .ok { span := span 0 3, value := .error } (missingState prior 1 [missingEvent]) ∧
      (missingState prior 1 [missingEvent]).diagnostics = prior ++ [missingEvent] ∧
      (missingState prior 1 [missingEvent]).peek? = some (sym 3 4 .semicolon) := by
  have parsed : NamedParameterTailTraceParses name.span none name name.span source 4
      (remainder missingTokens 1) (errorParameterTraceValue name.span) (remainder missingTokens 1) [missingEvent] :=
    .typeMissing (by simp [TokenKindAbsentAt, TokenAt, remainder, missingTokens, sym]) .emitted
  refine ⟨parsed, ?_, ?_, rfl⟩
  · exact (namedParameterTail_trace_success_state_iff name.span none name name.span
      (input := missingState prior 1 [])).mp parsed
  · simp only [missingState, state, State.diagnostics, List.reverse_append, List.reverse_reverse]

private def rejectedName : Identifier := { span := span 4 7, value := "a-b" }
private def rejectedNameToken : Token := { span := rejectedName.span, value := .identifier rejectedName.value }
private def rejectedTokens : List Token := [nameToken, sym 3 4 .colon, rejectedNameToken, sym 7 8 .dot, sym 8 9 .plus]
private def rejectedEvent : ParseDiagnostic := {
  span := rejectedName.span, kind := .invalidIdentifierHyphen rejectedName.value
}
private def failure : Failure := {
  span := span 8 9, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .typeExpr
}
private def rejectedState := state "arg:a-b.+" rejectedTokens 9

private theorem rejection_trace :
    NamedParameterTailTraceRejects name.span none name name.span source 9
      (remainder rejectedTokens 1) (remainder rejectedTokens 4) failure.toDiagnostic [rejectedEvent] := by
  let r := remainder rejectedTokens
  have head : IdentifierTraceParses (r 2) rejectedName (r 3) [rejectedEvent] :=
    .parsed ⟨⟨by change 2 < 5; decide, rfl⟩, rfl, rfl, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling rejectedName; decide))
  have tail : DottedIdentifierTailTraceRejects .typeExpr source 9 (r 3) (r 4) failure.toDiagnostic [] :=
    .componentRejected (span 7 8) ⟨⟨by change 3 < 5; decide, rfl⟩, rfl⟩
      (by simp [IdentifierAbsentAt, TokenAt, r, remainder, rejectedTokens, sym])
      (.reported (.token (current := sym 8 9 .plus) ⟨by change 4 < 5; decide, rfl⟩))
  have qualified : QualifiedNameTraceRejects .typeExpr source 9 (r 2) (r 4) failure.toDiagnostic [rejectedEvent] := by
    simpa only [List.append_nil] using QualifiedNameTraceRejects.tailRejected head tail
  have typed : TypeExprTraceRejects source 9 (r 2) (r 4) failure.toDiagnostic [rejectedEvent] :=
    TypeExprTraceRejects.roll (.selected .named
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (rejectedState [] 2 []) = .named from rfl))
      (.nameRejected qualified))
  exact .typeRejected (span 3 4) ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩ typed

theorem dotted_type_failure_has_no_finishing_event (prior : List ParseDiagnostic) :
    NamedParameterTailTraceRejects name.span none name name.span source 9
      (remainder rejectedTokens 1) (remainder rejectedTokens 4) failure.toDiagnostic [rejectedEvent] ∧
      namedParameterTail name.span none name name.span (rejectedState prior 1 []) =
        .reject failure (rejectedState prior 4 [rejectedEvent]) ∧
      (rejectedState prior 4 [rejectedEvent]).diagnostics = prior ++ [rejectedEvent] ∧
      (rejectedState prior 4 [rejectedEvent]).peek? = some (sym 8 9 .plus) ∧
      (rejectedState prior 4 [rejectedEvent]).window = { endIndex := 5, endByte := 9 } := by
  refine ⟨rejection_trace, ?_, ?_, rfl, rfl⟩
  · exact (namedParameterTail_trace_reject_failure_state_iff name.span none name name.span
      (input := rejectedState prior 1 [])).mp rejection_trace
  · simp only [rejectedState, state, State.diagnostics, List.reverse_append, List.reverse_reverse]

end Solcore.Test.SyntaxNamedParameterTailTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedParameterTraceProperties
/-! Public named-parameter recovery keeps core events when only the cursor is
rewound, commits its original report once, and appends the recovery event last.
Boundary and recovery rejection reports remain separate terminal payloads. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedParameterTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "public-parameter-trace.sol" }
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
private def recovered : FunctionParameter := { span := span 0 9, value := .error }
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

private theorem core_rejection : NamedParameterCoreTraceRejects source 99
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
  apply NamedParameterCoreTraceRejects.ordinary
    (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input tokens 5 []) = false from rfl))
  change OrdinaryNamedParameterTraceRejects source 99 (remainder tokens 5 0)
    (remainder tokens 5 2) coreFailure.toDiagnostic [nameEvent]
  simpa only [List.append_nil] using OrdinaryNamedParameterTraceRejects.tailRejected checked
    (.typeRejected (span 3 4) ⟨⟨by change 1 < 5; decide, rfl⟩, rfl⟩ typed)

private theorem recovery_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder tokens 5 0) recovered (remainder tokens 5 4) [recoveryEvent] := by
  have colon : TokenAt tokens.toArray 5 1 (symbol 3 4 .colon) := ⟨by decide, rfl⟩
  have plus : TokenAt tokens.toArray 5 2 (symbol 4 5 .plus) := ⟨by decide, rfl⟩
  have last : TokenAt tokens.toArray 5 3 skipped := ⟨by decide, rfl⟩
  refine ⟨.recovered (token := first) ⟨by change 0 < 5; decide, rfl⟩ ?_, rfl⟩
  exact .next (scan_continues colon (by decide) (by decide)) colon
    (.next (scan_continues plus (by decide) (by decide)) plus
      (.next (scan_continues last (by decide) (by decide)) last
        (.stop (.comma ⟨by change 4 < 5; decide, rfl⟩))))

private theorem public_recovered_trace : NamedParameterTraceParses source 99
    (remainder tokens 5 0) recovered (remainder tokens 5 4) events :=
  .recovered core_rejection (nonboundary (scan_continues (current := first)
    ⟨by change 0 < 5; decide, rfl⟩ (by decide) (by decide))) recovery_trace

private def boundaryTokens : List Token := [symbol 0 1 .comma]
private def boundaryFailure : Failure := {
  span := span 0 1, found := some (.symbol .comma)
  expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem boundary_trace : NamedParameterTraceRejects source 99
    (remainder boundaryTokens 1 0) (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] := by
  have core : NamedParameterCoreTraceRejects source 99 (remainder boundaryTokens 1 0)
      (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] :=
    .ordinary (ParameterDispatchTraceInternals.comptimeGuard_false_iff.mp (show
      ParameterDispatchTraceInternals.comptimeGuard (input boundaryTokens 1 []) = false from rfl))
      (.nameRejected (by simp [IdentifierAbsentAt, TokenAt, remainder, boundaryTokens, symbol])
        (.reported (.token (current := symbol 0 1 .comma) ⟨by change 0 < 1; decide, rfl⟩)))
  exact .boundary core (.comma ⟨by change 0 < 1; decide, rfl⟩)

private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .identifier, tail := [] }, context := .parameter
}
private theorem missing_trace : NamedParameterTraceRejects source 99
    (remainder [] 2 0) (remainder [] 2 0) missingFailure.toDiagnostic [missingFailure.toDiagnostic] := by
  have reported : RejectAtReports source 99 { head := .identifier, tail := [] } .parameter
      (remainder [] 2 0) missingFailure.toDiagnostic :=
    .reported (.missingToken (by change 0 < 2; decide) rfl)
  have core : NamedParameterCoreTraceRejects source 99 (remainder [] 2 0)
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
    NamedParameterTraceParses source 99 (remainder tokens 5 0) recovered (remainder tokens 5 4) events ∧
    NamedParameterTraceRejects source 99 (remainder boundaryTokens 1 0)
      (remainder boundaryTokens 1 0) boundaryFailure.toDiagnostic [] ∧
    NamedParameterTraceRejects source 99 (remainder [] 2 0) (remainder [] 2 0)
      missingFailure.toDiagnostic [missingFailure.toDiagnostic] :=
  ⟨public_recovered_trace, boundary_trace, missing_trace⟩

theorem core_failure_precedes_cursor_rewind (prior : List ParseDiagnostic) :
    FunctionParameterInternals.namedParameterCore (input tokens 5 prior) = .reject coreFailure
      { input tokens 5 prior with cursor := 2, diagnosticsRev := nameEvent :: prior.reverse } ∧
    parameterTraceRewind (remainder tokens 5 0) (remainder tokens 5 2) = remainder tokens 5 0 :=
  ⟨(FunctionParameterInternals.namedParameterCore_trace_reject_failure_state_iff
    (input := input tokens 5 prior)).mp core_rejection, rfl⟩

/-- Only the cursor is rewound: the checked-name event survives. Recovery
does not check either revisited `a-b` or skipped `c-d` again. -/
theorem public_recovery_retains_order (prior : List ParseDiagnostic) :
    namedParameter (input tokens 5 prior) = .ok recovered (final prior) ∧
    (final prior).diagnostics = prior ++ events ∧
    (final prior).peek? = some (symbol 9 10 .comma) := by
  refine ⟨(namedParameter_trace_success_state_iff (input := input tokens 5 prior)).mp public_recovered_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem public_recovery_preserves_prior_duplicates (prior : List ParseDiagnostic) :
    namedParameter (input tokens 5 (prior ++ [nameEvent, nameEvent])) =
      .ok recovered (final (prior ++ [nameEvent, nameEvent])) ∧
    (final (prior ++ [nameEvent, nameEvent])).diagnostics =
      prior ++ [nameEvent, nameEvent, nameEvent, coreFailure.toDiagnostic, recoveryEvent] := by
  have result := public_recovery_retains_order (prior ++ [nameEvent, nameEvent])
  exact ⟨result.1, by simpa only [events, List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

/-- Boundary rejection does not commit the core's terminal report. -/
theorem public_boundary_report_uncommitted (prior : List ParseDiagnostic) :
    namedParameter (input boundaryTokens 1 prior) = .reject boundaryFailure (input boundaryTokens 1 prior) ∧
    (input boundaryTokens 1 prior).diagnostics = prior := by
  refine ⟨(namedParameter_trace_reject_failure_state_iff
    (input := input boundaryTokens 1 prior)).mp boundary_trace, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- Numeric window membership without backing enters recovery. The core and
recovery reports have equal payloads here, but only the core report is committed. -/
theorem public_recovery_terminal_report_uncommitted (prior : List ParseDiagnostic) :
    namedParameter (input [] 2 prior) = .reject missingFailure
      { input [] 2 prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } ∧
    ({ input [] 2 prior with diagnosticsRev := missingFailure.toDiagnostic :: prior.reverse } : State).diagnostics =
      prior ++ [missingFailure.toDiagnostic] ∧
    (input [] 2 prior).cursor < (input [] 2 prior).window.endIndex ∧ (input [] 2 prior).peek? = none := by
  refine ⟨(namedParameter_trace_reject_failure_state_iff (input := input [] 2 prior)).mp missing_trace,
    ?_, by change 0 < 2; decide, rfl⟩
  simp only [State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- Mixed filtering keeps the protected core event while filtering only the
committed original report and recovery event under explicit conditions. -/
theorem recovery_suffix_conditionally_filtered (text : String) (lexical : List SourceSpan)
    (coreSuppressed : LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoverySuppressed : LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events [nameEvent] := by
  have filtered := namedParameterRecoveryTrace_cascadeFilters core_rejection text lexical
    (ParseDiagnosticCascadeFilters.drop ⟨by trivial, coreSuppressed⟩ .nil)
    (recovery_trace.cascade_dropped text lexical recoverySuppressed)
  simpa only [events, List.append_nil, List.cons_append, List.nil_append] using filtered

theorem recovery_suffix_retained_without_suppression (text : String) (lexical : List SourceSpan)
    (coreRetained : ¬ LexicalCascadeSuppresses text lexical coreFailure.span)
    (recoveryRetained : ¬ LexicalCascadeSuppresses text lexical recovered.span) :
    ParseDiagnosticCascadeFilters text lexical events events :=
  namedParameterRecoveryTrace_cascadeFilters core_rejection text lexical
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

end Solcore.Test.SyntaxNamedParameterTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxOptionalLambdaReturnTypeTraceProperties
/-! Narrow optional-return consumers. Present-arrow examples are conditional
on the actual type result, not claims of concrete general type trace coverage. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxOptionalLambdaReturnTypeTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.ExpressionAtomInternals
open Solcore.Syntax.DeclarativeGrammar

theorem absent_arrow_has_no_rejection {input : State}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .arrow)) :
    optionalLambdaReturnType input = .ok none input ∧
      ∀ failure rejected, optionalLambdaReturnType input ≠ .reject failure rejected := by
  have result := optionalLambdaReturnType_eq_none_of_absent absent
  exact ⟨result, by intro failure rejected impossible; rw [result] at impossible; cases impossible⟩

theorem selected_arrow_preserves_success_state_and_duplicate_events
    {input output : State} {span : SourceSpan} {type : TypeExpr} (event : ParseDiagnostic)
    (arrow : TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .arrow })
    (child : typeExpr { input with cursor := input.cursor + 1 } = .ok type output)
    (events : output.diagnostics = input.diagnostics ++ [event, event]) :
    optionalLambdaReturnType input = .ok (some type) output ∧
      output.diagnostics = input.diagnostics ++ [event, event] := by
  exact ⟨by rw [optionalLambdaReturnType_eq_of_present arrow, child], events⟩

theorem selected_arrow_preserves_rejection_state_and_duplicate_events
    {input rejected : State} {span : SourceSpan} {failure : Failure} (event : ParseDiagnostic)
    (arrow : TokenAt input.tokens input.window.endIndex input.cursor { span, value := .symbol .arrow })
    (child : typeExpr { input with cursor := input.cursor + 1 } = .reject failure rejected)
    (events : rejected.diagnostics = input.diagnostics ++ [event, event]) :
    optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.diagnostics = input.diagnostics ++ [event, event] := by
  exact ⟨by rw [optionalLambdaReturnType_eq_of_present arrow, child], events⟩

theorem successful_optional_return_keeps_complete_suffix
    {typeTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {type : Option TypeExpr} {trace : List ParseDiagnostic}
    (childProtected : ∀ {input type output trace}, typeTrace source endByte input type output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map LexicalDiagnostic.span) trace trace)
    (parsed : OptionalLambdaReturnTypeTraceParses typeTrace source endByte input type output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected)

theorem rejected_optional_return_keeps_complete_suffix
    {typeRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (childProtected : ∀ {input rejected diagnostic trace},
      typeRejects source endByte input rejected diagnostic trace →
        ParseDiagnosticCascadeFilters file.content (lexical.map LexicalDiagnostic.span) trace trace)
    (rejection : OptionalLambdaReturnTypeTraceRejects typeRejects source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (rejection.cascadeFilters childProtected)

end Solcore.Test.SyntaxOptionalLambdaReturnTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParameterListTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterListTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParameterNameDispatchTraceProperties
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
end

section
-- leanmerge: from Solcore.Test.SyntaxParameterRecoveryTraceProperties
/-! Standalone recovery consumes its mandatory first token before testing a
boundary. Independent scans drive complete replies, including malformed token
windows; recovery events have conditional, not protected, cascade behavior. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParameterRecoveryTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "parameter-recovery-trace.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def symbol (startByte endByte : Nat) (kind : Symbol) : Token := {
  span := span startByte endByte, value := .symbol kind
}
private def skipped : Token := { span := span 1 4, value := .identifier "a-b" }
private def scanTokens : List Token := [symbol 0 1 .comma, skipped, symbol 4 5 .rightParen, symbol 5 6 .plus]
private def commaTokens : List Token := [symbol 0 1 .rightParen, symbol 1 2 .comma, symbol 2 3 .plus]
private def sparseTokens : List Token := [symbol 0 1 .plus]
private def remainder (tokens : List Token) (endIndex cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex, cursor
}
private def input (tokens : List Token) (endIndex cursor : Nat) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }, tokens := tokens.toArray, cursor
  window := { endIndex, endByte := 99 }, diagnosticsRev := prior.reverse
}
private def recovered (startByte endByte : Nat) : FunctionParameter := {
  span := span startByte endByte, value := .error
}
private def event (startByte endByte : Nat) : ParseDiagnostic := parameterRecoveryTraceEvent (span startByte endByte)
private def final (tokens : List Token) (endIndex cursor : Nat) (diagnostic : ParseDiagnostic)
    (prior : List ParseDiagnostic) : State := {
  input tokens endIndex cursor prior with diagnosticsRev := diagnostic :: prior.reverse
}
private def missingFailure : Failure := {
  span := span 99 99, found := none, expected := { head := .identifier, tail := [] }, context := .parameter
}

private theorem scan_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder scanTokens 4 0) (recovered 0 4) (remainder scanTokens 4 2) [event 0 4] := by
  have continues : ¬ FunctionParameterRecoveryStops (remainder scanTokens 4 1) := by
    intro stops
    cases stops with
    | windowEnd atEnd => change 4 ≤ 1 at atEnd; omega
    | comma token => simp [TokenAt, remainder, scanTokens, skipped] at token
    | rightParen token => simp [TokenAt, remainder, scanTokens, skipped] at token
    | missingToken inside missing => simp [remainder, scanTokens] at missing
  refine ⟨.recovered (token := symbol 0 1 .comma) ⟨by change 0 < 4; decide, rfl⟩ ?_, rfl⟩
  exact .next continues (token := skipped) ⟨by change 1 < 4; decide, rfl⟩
    (.stop (.rightParen ⟨by change 2 < 4; decide, rfl⟩))

private theorem comma_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder commaTokens 3 0) (recovered 0 1) (remainder commaTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .rightParen) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.comma ⟨by change 1 < 3; decide, rfl⟩)), rfl⟩

/-- Initial comma is consumed, the intervening hyphen identifier is skipped
without checking it, and the later right parenthesis is left unread. -/
theorem mandatory_comma_then_rightParen_stop (prior : List ParseDiagnostic) :
    recoverParameter (input scanTokens 4 0 prior) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) prior) ∧
    (final scanTokens 4 2 (event 0 4) prior).diagnostics = prior ++ [event 0 4] ∧
    (final scanTokens 4 2 (event 0 4) prior).peek? = some (symbol 4 5 .rightParen) := by
  refine ⟨(recoverParameter_trace_success_state_iff (input := input scanTokens 4 0 prior)).mp scan_trace, ?_, rfl⟩
  simp only [final, State.diagnostics, List.reverse_cons, List.reverse_reverse]

/-- The same mandatory-consumption rule applies to an initial right parenthesis;
only the following comma is a scan stop. -/
theorem mandatory_rightParen_then_comma_stop (prior : List ParseDiagnostic) :
    recoverParameter (input commaTokens 3 0 prior) = .ok (recovered 0 1)
      (final commaTokens 3 1 (event 0 1) prior) ∧
    (final commaTokens 3 1 (event 0 1) prior).peek? = some (symbol 1 2 .comma) :=
  ⟨(recoverParameter_trace_success_state_iff (input := input commaTokens 3 0 prior)).mp comma_trace, rfl⟩

private theorem sparse_trace : FunctionParameterRecoveryTraceParses source 99
    (remainder sparseTokens 3 0) (recovered 0 1) (remainder sparseTokens 3 1) [event 0 1] :=
  ⟨.recovered (token := symbol 0 1 .plus) ⟨by change 0 < 3; decide, rfl⟩
    (.stop (.missingToken (by change 1 < 3; decide) rfl)), rfl⟩

private theorem sparse_rejection : FunctionParameterRecoveryTraceRejects source 99
    (remainder sparseTokens 3 1) (remainder sparseTokens 3 1) missingFailure.toDiagnostic [] :=
  ⟨.missingToken (by change 1 < 3; decide) rfl,
    .reported (.missingToken (by change 1 < 3; decide) rfl), rfl⟩

/-- Missing backing inside the numeric window ends an established scan, but
rejects if recovery has not yet obtained its mandatory first token. -/
theorem missing_backing_stop_versus_initial_rejection (prior : List ParseDiagnostic) :
    recoverParameter (input sparseTokens 3 0 prior) = .ok (recovered 0 1)
      (final sparseTokens 3 1 (event 0 1) prior) ∧
    recoverParameter (input sparseTokens 3 1 prior) = .reject missingFailure (input sparseTokens 3 1 prior) ∧
    (input sparseTokens 3 1 prior).cursor < (input sparseTokens 3 1 prior).window.endIndex ∧
    (input sparseTokens 3 1 prior).peek? = none ∧
    (input sparseTokens 3 1 prior).diagnostics = prior := by
  refine ⟨(recoverParameter_trace_success_state_iff (input := input sparseTokens 3 0 prior)).mp sparse_trace,
    (recoverParameter_trace_reject_failure_state_iff (input := input sparseTokens 3 1 prior)).mp sparse_rejection,
    by change 1 < 3; decide, rfl, ?_⟩
  simp only [input, State.diagnostics, List.reverse_reverse]

/-- A window end likewise rejects without consuming a hidden backing token. -/
theorem hidden_first_token_rejects_unchanged (prior : List ParseDiagnostic) :
    (input sparseTokens 0 0 prior).tokens[0]? = some (symbol 0 1 .plus) ∧
    recoverParameter (input sparseTokens 0 0 prior) = .reject missingFailure (input sparseTokens 0 0 prior) := by
  refine ⟨rfl, (recoverParameter_trace_reject_failure_state_iff (input := input sparseTokens 0 0 prior)
    (after := remainder sparseTokens 0 0) (failure := missingFailure) (trace := [])).mp ?_⟩
  exact ⟨.windowEnd (by change 0 ≤ 0; decide), .reported (.windowEnd (by change 0 ≤ 0; decide)), rfl⟩

/-- Standalone recovery appends only its own event to an already committed
original failure. The original complete report is neither replayed nor removed. -/
theorem committed_failure_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    recoverParameter (input scanTokens 4 0 (prior ++ [original.toDiagnostic])) = .ok (recovered 0 4)
      (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])) ∧
    (final scanTokens 4 2 (event 0 4) (prior ++ [original.toDiagnostic])).diagnostics =
      prior ++ [original.toDiagnostic, event 0 4] := by
  have result := mandatory_comma_then_rightParen_stop (prior ++ [original.toDiagnostic])
  exact ⟨result.1, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1⟩

theorem recovery_event_kept_when_not_suppressed (text : String) (lexical : List SourceSpan)
    (retained : ¬ LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [event 0 4] :=
  scan_trace.cascade_kept text lexical retained

theorem recovery_event_dropped_when_suppressed (text : String) (lexical : List SourceSpan)
    (suppressed : LexicalCascadeSuppresses text lexical (span 0 4)) :
    ParseDiagnosticCascadeFilters text lexical [event 0 4] [] :=
  scan_trace.cascade_dropped text lexical suppressed

/-- Concrete filtering shows why a recovery event cannot use an unconditional
protected-suffix theorem: a matching lexical range removes it. -/
theorem recovery_event_is_conditionally_filtered (text : String) :
    filterParseDiagnostics { id := source, content := text } [] [event 0 4] = [event 0 4] ∧
    filterParseDiagnostics { id := source, content := text }
      [{ span := span 0 4, kind := .invalidToken }] [event 0 4] = [] := by
  constructor
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_kept_when_not_suppressed text [] (by simp [LexicalCascadeSuppresses]))
  · exact filterParseDiagnostics_eq_of_cascadeFilters _ _
      (recovery_event_dropped_when_suppressed text [span 0 4]
        ⟨span 0 4, by simp, ⟨rfl, .inl rfl⟩⟩)

end Solcore.Test.SyntaxParameterRecoveryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxLambdaParameterRecoveryTraceProperties
/-! Standalone lambda recovery changes only the error AST carrier. Independent
traces restore both complete replies; existing function-recovery fixtures are
reused to test delimiter consumption, missing backing, and committed reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxLambdaParameterRecoveryTraceProperties

open Syntax Syntax.Parser Syntax.DeclarativeGrammar
open FunctionParameterInternals LambdaParameterInternals

private theorem retag_success {input output : State} {value : FunctionParameter}
    (result : recoverParameter input = .ok value output) :
    recoverLambdaParameter input = .ok { span := value.span, value := .error } output := by
  simp only [recoverLambdaParameter, result]

private theorem retag_rejection {input rejected : State} {failure : Failure}
    (result : recoverParameter input = .reject failure rejected) :
    recoverLambdaParameter input = .reject failure rejected := by
  simp only [recoverLambdaParameter, result]

/-- One independent witness restores both complete replies with exactly the
same source, carrier, window, cursor, and ordered diagnostic suffix. -/
theorem independent_trace_restores_both_replies
    {input : State} {value : FunctionParameter} {after : Remainder} {trace : List ParseDiagnostic}
    (parsed : FunctionParameterRecoveryTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    LambdaParameterRecoveryTraceParses input.file.id input.window.endByte input.declarativeRemainder
      { span := value.span, value := .error } after trace ∧
    recoverParameter input = .ok value (input.traceResult after trace) ∧
    recoverLambdaParameter input = .ok { span := value.span, value := .error } (input.traceResult after trace) ∧
    (input.traceResult after trace).diagnostics = input.diagnostics ++ [parameterRecoveryTraceEvent value.span] := by
  refine ⟨.recovered parsed, recoverParameter_trace_success_state_iff.mp parsed,
    recoverLambdaParameter_trace_success_state_iff.mp (.recovered parsed), ?_⟩
  rw [State.traceResult_diagnostics, parsed.2]

/-- A terminal recovery Failure is forwarded intact and is not committed by
either wrapper. This does not remove an equal report already present in input. -/
theorem independent_rejection_restores_both_replies
    {input : State} {after : Remainder} {failure : Failure} {trace : List ParseDiagnostic}
    (rejected : FunctionParameterRecoveryTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    recoverParameter input = .reject failure (input.traceResult after trace) ∧
    recoverLambdaParameter input = .reject failure (input.traceResult after trace) ∧
    (input.traceResult after trace).diagnostics = input.diagnostics := by
  refine ⟨recoverParameter_trace_reject_failure_state_iff.mp rejected,
    recoverLambdaParameter_trace_reject_failure_state_iff.mp rejected, ?_⟩
  rw [State.traceResult_diagnostics, rejected.2.2, List.append_nil]

/-- Reuse the existing comma / skipped hyphen name / right-parenthesis scan:
the mandatory comma is consumed, while the later right parenthesis is not. -/
theorem mandatory_comma_is_consumed (prior : List ParseDiagnostic) :
    ∃ (input output : State) (value : FunctionParameter),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      input.cursor = 0 ∧ input.peek?.map (·.value) = some (.symbol .comma) ∧
      output.cursor = 2 ∧ output.peek?.map (·.value) = some (.symbol .rightParen) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 4 ∧
      output.diagnostics = prior ++ [parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.mandatory_comma_then_rightParen_stop prior
  exact ⟨_, _, _, result.1, retag_success result.1, rfl, rfl, rfl, rfl, rfl, rfl, result.2.1⟩

/-- Initial right parenthesis has the same mandatory-consumption behavior;
the following comma remains at the identical output State in both parsers. -/
theorem mandatory_rightParen_is_consumed (prior : List ParseDiagnostic) :
    ∃ (input output : State) (value : FunctionParameter),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      input.cursor = 0 ∧ input.peek?.map (·.value) = some (.symbol .rightParen) ∧
      output.cursor = 1 ∧ output.peek?.map (·.value) = some (.symbol .comma) ∧
      value.span.startByte = 0 ∧ value.span.endByte = 1 ∧
      output.diagnostics = prior ++ [parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.mandatory_rightParen_then_comma_stop prior
  refine ⟨_, _, _, result.1, retag_success result.1, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  change (parameterRecoveryTraceEvent _ :: prior.reverse).reverse = _
  simp only [List.reverse_cons, List.reverse_reverse]
  rfl

/-- With numeric endIndex 3 but one backing token, an established scan stops
at cursor 1; a fresh recovery there rejects and leaves all prior events intact. -/
theorem missing_backing_scan_stop_and_initial_rejection (prior : List ParseDiagnostic) :
    ∃ (input output missing : State) (value : FunctionParameter) (failure : Failure),
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      recoverParameter missing = .reject failure missing ∧
      recoverLambdaParameter missing = .reject failure missing ∧
      input.cursor = 0 ∧ output.cursor = 1 ∧ missing.cursor = 1 ∧
      missing.window.endIndex = 3 ∧ missing.peek? = none ∧ missing.diagnostics = prior ∧
      failure.expected = { head := .identifier, tail := [] } ∧ failure.context = .parameter ∧
      failure.found = none := by
  have result := SyntaxParameterRecoveryTraceProperties.missing_backing_stop_versus_initial_rejection prior
  exact ⟨_, _, _, _, _, result.1, retag_success result.1, result.2.1, retag_rejection result.2.1,
    rfl, rfl, rfl, rfl, result.2.2.2.1, result.2.2.2.2, rfl, rfl, rfl⟩

/-- A token hidden by endIndex zero is not the mandatory first token, even
though the backing array contains it. Both complete rejected States are input. -/
theorem hidden_first_token_is_not_consumed (prior : List ParseDiagnostic) :
    ∃ (input : State) (token : Token) (failure : Failure),
      input.cursor = 0 ∧ input.window.endIndex = 0 ∧ input.tokens[0]? = some token ∧
      token.value = .symbol .plus ∧
      recoverParameter input = .reject failure input ∧
      recoverLambdaParameter input = .reject failure input := by
  have result := SyntaxParameterRecoveryTraceProperties.hidden_first_token_rejects_unchanged prior
  exact ⟨_, _, _, rfl, rfl, result.1, rfl, result.2, retag_rejection result.2⟩

/-- The previously committed complete report remains once before recovery's
event. Arbitrary prior duplicates are not deduplicated by the lambda retag. -/
theorem committed_report_is_not_reemitted (prior : List ParseDiagnostic) (original : Failure) :
    ∃ (input output : State) (value : FunctionParameter),
      input.diagnostics = prior ++ [original.toDiagnostic] ∧
      recoverParameter input = .ok value output ∧
      recoverLambdaParameter input = .ok { span := value.span, value := .error } output ∧
      output.diagnostics = prior ++ [original.toDiagnostic, parameterRecoveryTraceEvent value.span] := by
  have result := SyntaxParameterRecoveryTraceProperties.committed_failure_is_not_reemitted prior original
  refine ⟨_, _, _, ?_, result.1, retag_success result.1, result.2⟩
  change (prior ++ [original.toDiagnostic]).reverse.reverse = _
  exact List.reverse_reverse _

/-- Error retagging does not turn the recovery event into a protected event:
the same independently specified trace may be retained or dropped conditionally. -/
theorem recovery_trace_has_conditional_filtering
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {value : LambdaParameter} {trace : List ParseDiagnostic}
    (parsed : LambdaParameterRecoveryTraceParses source endByte input value output trace)
    (text : String) (lexical : List SourceSpan) :
    (¬ LexicalCascadeSuppresses text lexical value.span → ParseDiagnosticCascadeFilters text lexical trace trace) ∧
    (LexicalCascadeSuppresses text lexical value.span → ParseDiagnosticCascadeFilters text lexical trace []) :=
  ⟨parsed.cascade_kept text lexical, parsed.cascade_dropped text lexical⟩

/-- The concrete 0..4 scan supplies a lambda trace whose recovered event is
kept without lexical errors but removed by a lexical error on the same span. -/
theorem concrete_recovery_event_is_conditionally_filtered (text : String) :
    ∃ (source : SourceId) (input output : Remainder) (value : LambdaParameter),
      LambdaParameterRecoveryTraceParses source 99 input value output [parameterRecoveryTraceEvent value.span] ∧
      value.value = .error ∧ value.span.startByte = 0 ∧ value.span.endByte = 4 ∧
      filterParseDiagnostics { id := source, content := text } []
        [parameterRecoveryTraceEvent value.span] = [parameterRecoveryTraceEvent value.span] ∧
      filterParseDiagnostics { id := source, content := text }
        [{ span := value.span, kind := .invalidToken }] [parameterRecoveryTraceEvent value.span] = [] := by
  have tested := SyntaxParameterRecoveryTraceProperties.mandatory_comma_then_rightParen_stop []
  rcases recoverParameter_trace_success_sound tested.1 with ⟨trace, parsed, _⟩
  have traceEq := parsed.2
  rw [traceEq] at parsed
  have filtered := SyntaxParameterRecoveryTraceProperties.recovery_event_is_conditionally_filtered text
  exact ⟨_, _, _, _, .recovered parsed, rfl, rfl, rfl, filtered.1, filtered.2⟩

end Solcore.Test.SyntaxLambdaParameterRecoveryTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLambdaParameterCoreTotalityProperties
set_option autoImplicit false
namespace Solcore.Test.SyntaxParserLambdaParameterCoreTotalityProperties
open Solcore.Syntax.Parser
example := @LambdaParameterInternals.lambdaParameterCore_invariantFreeOnValid
example := @LambdaParameterInternals.lambdaParameterCore_cursor_lt_onSuccess
example := @lambdaParameter_invariantFreeOnValid
example := @lambdaParameter_ne_invariant
example := @lambdaParameter_cursor_lt_onSuccess
example := @lambdaParameter_elementTotalityContract
end Solcore.Test.SyntaxParserLambdaParameterCoreTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLambdaParameterExactnessProperties
/-! External consumers of exact public lambda-parameter outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLambdaParameterExactnessProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @DeclarativeGrammar.lambdaParameterPublicExactOutcomeSpec
example := @DeclarativeGrammar.LambdaParameterOrdinaryParses.result_unique
example := @DeclarativeGrammar.LambdaParameterRejects.output_unique

example : DeclarativeGrammar.ExactDeterministicOutcomeSpec
    (DeclarativeGrammar.LambdaParameterOrdinaryParses
      DeclarativeGrammar.TypeExprOrdinaryParses DeclarativeGrammar.TypeExprRejects)
    (DeclarativeGrammar.LambdaParameterRejects DeclarativeGrammar.TypeExprRejects) :=
  lambdaParameter_exactOutcomeSpec

example {input leftOutput rightOutput : State} {left right : LambdaParameter}
    (leftResult : lambdaParameter input = .ok left leftOutput)
    (rightResult : lambdaParameter input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_success_result_unique leftResult rightResult

example {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : lambdaParameter input = .reject leftFailure leftOutput)
    (rightResult : lambdaParameter input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  lambdaParameter_reject_output_unique leftResult rightResult

end Solcore.Test.SyntaxParserLambdaParameterExactnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserLambdaParameterTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserLambdaParameterTotalityProperties

open Solcore.Syntax.Parser

example := @FunctionParameterInternals.recoverParameter_cursor_lt_onSuccess
example := @LambdaParameterInternals.recoverLambdaParameter_ordinary
example := @LambdaParameterInternals.recoverLambdaParameter_invariantFreeOnValid
example := @LambdaParameterInternals.recoverLambdaParameter_ne_invariant
example := @LambdaParameterInternals.recoverLambdaParameter_cursor_lt_onSuccess
example := @lambdaParameter_invariantFreeOnValid_of_core
example := @lambdaParameter_ne_invariant_of_core
example := @lambdaParameter_cursor_lt_onSuccess_of_core
example := @lambdaParameter_elementTotalityContract_of_core

end Solcore.Test.SyntaxParserLambdaParameterTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserNamedParameterTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserNamedParameterTotalityProperties

open Solcore.Syntax.Parser

example := @FunctionParameterInternals.namedParameterCore_invariantFreeOnValid
example := @FunctionParameterInternals.namedParameterCore_cursor_lt_onSuccess
example := @namedParameter_ordinary
example := @namedParameter_invariantFreeOnValid
example := @namedParameter_ne_invariant
example := @namedParameter_cursor_lt_onSuccess
example := @namedParameter_elementTotalityContract

end Solcore.Test.SyntaxParserNamedParameterTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserParameterRecoveryTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserParameterRecoveryTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.FunctionParameterInternals

example : Parser.Ordinary recoverParameter := recoverParameter_ordinary

example (state : State) (error : ParserInvariantError) :
    recoverParameter state ≠ .invariant error :=
  recoverParameter_ne_invariant state error

end Solcore.Test.SyntaxParserParameterRecoveryTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypedParameterFinishingTraceProperties
/-! Finishing-only consumers retain complete states and exact parameter ASTs.
An existing checked-type event is already in the input history: finishing adds
only its own suffix, including a repeated constraint when identical events are
already present. Only an outer comptime type triggers that suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypedParameterFinishingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.FunctionParameterInternals

private def source : SourceId := { origin := .main, path := "parameter-finishing.sol" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def marker : Option SourceSpan := some (span 0 8)
private def name : Identifier := { span := span 9 12, value := "arg" }
private def typeName : Identifier := { span := span 22 25, value := "a-b" }
private def innerType : TypeExpr := namedTypeTraceValue (tracedQualifiedName typeName []) none
private def comptimeType : TypeExpr := {
  span := span 13 27, value := .comptime (span 13 21) (span 21 27) innerType
}
private def proxyType : TypeExpr := {
  span := span 12 27, value := .proxy (span 12 13) comptimeType
}
private def comptimeParameter : FunctionParameter := {
  span := span 0 27, value := .typed marker name comptimeType
}
private def proxyParameter : FunctionParameter := {
  span := span 0 27, value := .typed marker name proxyType
}
private def typeEvent : ParseDiagnostic := {
  span := typeName.span, kind := .invalidIdentifierHyphen typeName.value
}
private def finishingEvent : ParseDiagnostic := {
  span := comptimeType.span, kind := .constraintViolation .comptimeTypeInParameter
}
private def seed (base : State) (prior : List ParseDiagnostic) : State := {
  base with diagnosticsRev := prior.reverse
}
private def finished (base : State) (prior : List ParseDiagnostic) : State := {
  seed base (prior ++ [typeEvent]) with
  diagnosticsRev := [finishingEvent] ++ (prior ++ [typeEvent]).reverse
}

private theorem comptime_events : TypedParameterFinishingTrace comptimeType [finishingEvent] :=
  .comptime (by simp [ParameterTypeAllowed, comptimeType])

theorem outer_comptime_adds_only_finishing_suffix (base : State) (prior : List ParseDiagnostic) :
    TypedParameterFinishingTrace comptimeType [finishingEvent] ∧
      finishTypedParameter (span 0 8) marker name comptimeType (seed base (prior ++ [typeEvent])) =
        .ok comptimeParameter (finished base prior) ∧
      (finished base prior).diagnostics = prior ++ [typeEvent, finishingEvent] ∧
      (finished base prior).file = base.file ∧ (finished base prior).tokens = base.tokens ∧
      (finished base prior).cursor = base.cursor ∧ (finished base prior).window = base.window := by
  refine ⟨comptime_events, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · exact finishTypedParameter_eq_ok_of_trace (span 0 8) marker name comptimeType
      (seed base (prior ++ [typeEvent])) comptime_events
  · simp only [finished, State.diagnostics, List.reverse_append, List.reverse_reverse,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]

theorem duplicate_constraints_remain_ordered (base : State) (prior : List ParseDiagnostic) :
    finishTypedParameter (span 0 8) marker name comptimeType
        (seed base (prior ++ [finishingEvent, finishingEvent, typeEvent])) =
      .ok comptimeParameter (finished base (prior ++ [finishingEvent, finishingEvent])) ∧
      (finished base (prior ++ [finishingEvent, finishingEvent])).diagnostics =
        prior ++ [finishingEvent, finishingEvent, typeEvent, finishingEvent] := by
  have result := outer_comptime_adds_only_finishing_suffix base (prior ++ [finishingEvent, finishingEvent])
  exact ⟨by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.1,
    by simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2.2.1⟩

theorem proxy_of_comptime_is_silent (base : State) (prior : List ParseDiagnostic) :
    TypedParameterFinishingTrace proxyType [] ∧
      finishTypedParameter (span 0 8) marker name proxyType (seed base (prior ++ [typeEvent])) =
        .ok proxyParameter (seed base (prior ++ [typeEvent])) ∧
      (seed base (prior ++ [typeEvent])).diagnostics = prior ++ [typeEvent] := by
  have events : TypedParameterFinishingTrace proxyType [] := .ordinary (by trivial)
  refine ⟨events, ?_, ?_⟩
  · exact finishTypedParameter_eq_ok_of_trace (span 0 8) marker name proxyType
      (seed base (prior ++ [typeEvent])) events
  · simp only [seed, State.diagnostics, List.reverse_reverse]

private theorem exact_error (base : State) (prior : List ParseDiagnostic)
    (errorSpan : SourceSpan) (constraint : ParseConstraint) :
    ∃ output, errorParameter errorSpan constraint (seed base prior) =
      .ok { span := errorSpan, value := .error } output ∧
      output = { seed base prior with diagnosticsRev :=
        [{ span := errorSpan, kind := .constraintViolation constraint }] ++ prior.reverse } ∧
      output.diagnostics = prior ++ [{ span := errorSpan, kind := .constraintViolation constraint }] := by
  refine ⟨_, errorParameter_eq_ok_of_trace errorSpan constraint (seed base prior) .emitted, rfl, ?_⟩
  simp only [seed, State.diagnostics, List.reverse_append, List.reverse_reverse]

theorem missing_named_type_keeps_error_span (base : State) (prior : List ParseDiagnostic) :
    ErrorParameterFinishingTrace name.span .namedParameterRequiresType [{
      span := name.span, kind := .constraintViolation .namedParameterRequiresType
    }] ∧
      ∃ output, errorParameter name.span .namedParameterRequiresType (seed base prior) =
        .ok { span := span 9 12, value := .error } output ∧
        output = { seed base prior with diagnosticsRev :=
          [{ span := span 9 12, kind := .constraintViolation .namedParameterRequiresType }] ++ prior.reverse } ∧
        output.diagnostics = prior ++ [{ span := span 9 12, kind := .constraintViolation .namedParameterRequiresType }] :=
  ⟨.emitted, exact_error base prior name.span .namedParameterRequiresType⟩

theorem missing_comptime_type_keeps_covering_span (base : State) (prior : List ParseDiagnostic) :
    ErrorParameterFinishingTrace (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType [{
      span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType
    }] ∧
      ∃ output, errorParameter (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType
          (seed base prior) = .ok { span := span 0 12, value := .error } output ∧
        output = { seed base prior with diagnosticsRev :=
          [{ span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType }] ++ prior.reverse } ∧
        output.diagnostics = prior ++ [{ span := span 0 12, kind := .constraintViolation .comptimeParameterRequiresType }] :=
  ⟨.emitted, exact_error base prior (SourceSpan.cover (span 0 8) name.span) .comptimeParameterRequiresType⟩

end Solcore.Test.SyntaxTypedParameterFinishingTraceProperties
end
