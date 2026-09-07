import Solcore.Syntax.Parser.LambdaParameterRawTraceStateProperties
import Solcore.Syntax.Parser.ParameterDispatchTraceProperties

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
