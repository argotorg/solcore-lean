import Solcore.Syntax.Parser.NamedParameterTailTraceStateProperties

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
