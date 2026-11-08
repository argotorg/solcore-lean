import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Test.Syntax.Recovery
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Parser.Internal.ParameterSoundness
import Solcore.Syntax.Parser.Internal.SignatureSoundness
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Parser.Internal.ParameterTotality
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.TypeFormTotality
import Solcore.Syntax.Parser.Internal.TypeBasics
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Parser.Internal.TypeTotality
import Solcore.Syntax.Parser
import Solcore.Syntax.Lexer

/-!
# Type syntax tests

Type expressions and their traces, named and mapping types, qualified names, generic parameters
and predicates.
-/

section
-- leanmerge: from Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
/-! Reusable concrete type-expression leaves: one checked identifier with no
dotted tail or arguments. Positive fuel reaches the real named-type dispatch,
without evaluating the whole parser or assuming anything about its child. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem checked_name_type_with_positive_fuel
    (fuel : Nat) {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span := name.span, value := .identifier name.value })
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (dotAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot))
    (argumentsAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .less))
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    typeExprWithFuel (fuel + 1) input =
      .ok (namedTypeTraceValue (tracedQualifiedName name []) none)
        { input with cursor := input.cursor + 1, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have nameParsed : QualifiedNameTraceParses input.file.id input.window.endByte input.declarativeRemainder
      (tracedQualifiedName name []) { input.declarativeRemainder with cursor := input.cursor + 1 } trace := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed
      (source := input.file.id) (endByte := input.window.endByte)
      (IdentifierTraceParses.parsed (input := input.declarativeRemainder)
        (output := { input.declarativeRemainder with cursor := input.cursor + 1 })
        ⟨token, rfl, rfl, rfl⟩ diagnostics)
      (DottedIdentifierTailTraceParses.done
        (input := { input.declarativeRemainder with cursor := input.cursor + 1 }) dotAbsent)
  have nameResult := qualifiedName_eq_ok_of_trace .typeExpr .typeExpr nameParsed
  let afterName : State := { input with
    cursor := input.cursor + 1
    diagnosticsRev := trace.reverse ++ input.diagnosticsRev }
  change qualifiedName .typeExpr .typeExpr input = .ok (tracedQualifiedName name []) afterName at nameResult
  have argumentsResult := parseNamedTypeArguments_eq_none_of_absent (typeExprWithFuel fuel)
    (input := afterName) argumentsAbsent
  have finishing : NamedTypeFinishingTrace (tracedQualifiedName name []) none [] := by
    apply NamedTypeFinishingTrace.ordinary
    intro mapping
    exact notMapping mapping.2
  have finishResult := finishNamedType_eq_ok_of_trace (tracedQualifiedName name []) none afterName finishing
  change finishNamedType (tracedQualifiedName name []) none afterName =
    .ok (namedTypeTraceValue (tracedQualifiedName name []) none) afterName at finishResult
  have namedResult : parseNamedType (typeExprWithFuel fuel) input =
      .ok (namedTypeTraceValue (tracedQualifiedName name []) none) afterName := by
    simpa only [parseNamedType, bind, nameResult, argumentsResult] using finishResult
  have current : input.peek? = some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, token.1, if_true, token.2]
  have noComptime : isContextual input .comptime = false := by
    simp [isContextual, State.peekKind?, current, TokenKind.isContextual, notComptime]
  have noMapping : isContextual input .mapping = false := by
    simp [isContextual, State.peekKind?, current, TokenKind.isContextual, notMapping]
  have noFunction : isKeyword input .functionKw = false := by
    simp only [isKeyword, State.peekKind?, current, Option.map_some]; rfl
  have noProxy : isSymbol input .at = false := by
    simp only [isSymbol, State.peekKind?, current, Option.map_some]; rfl
  have noTuple : isSymbol input .leftParen = false := by
    simp only [isSymbol, State.peekKind?, current, Option.map_some]; rfl
  have named : isIdentifier input = true := by
    simp only [isIdentifier, State.peekKind?, current, Option.map_some]
  simpa only [typeExprWithFuel, noFunction, noComptime, noMapping, noProxy, noTuple,
    named, Bool.false_and, Bool.false_eq_true, if_false, if_true] using namedResult

theorem checked_name_type
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    (token : TokenAt input.tokens input.window.endIndex input.cursor
      { span := name.span, value := .identifier name.value })
    (diagnostics : IdentifierDiagnosticTrace name trace)
    (dotAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .dot))
    (argumentsAbsent : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 1) (.symbol .less))
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    typeExpr input = .ok (namedTypeTraceValue (tracedQualifiedName name []) none)
      { input with cursor := input.cursor + 1, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } :=
  checked_name_type_with_positive_fuel input.remainingCount token diagnostics dotAbsent argumentsAbsent notComptime notMapping

end Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxCheckedTypeListTraceSupport
/-! A concrete checked-name type child inside a singleton trailing list. The
carrier, source, active window, initial cursor, and earlier diagnostics remain
arbitrary; this supplies real execution without general type-trace contracts. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxCheckedTypeListTraceSupport

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport
open Solcore.Test.SyntaxDelimitedTrailingSuccessTraceProperties

theorem singleton_trailing_checked_type_list
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    {openingSpan commaSpan closingSpan : SourceSpan}
    (opening : TokenAt input.tokens input.window.endIndex input.cursor
      { span := openingSpan, value := .symbol .leftParen })
    (nameAt : TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := name.span, value := .identifier name.value })
    (comma : TokenAt input.tokens input.window.endIndex (input.cursor + 2)
      { span := commaSpan, value := .symbol .comma })
    (closing : TokenAt input.tokens input.window.endIndex (input.cursor + 3)
      { span := closingSpan, value := .symbol .rightParen })
    (nameTrace : IdentifierDiagnosticTrace name trace)
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr input =
      .ok {
        span := SourceSpan.cover openingSpan closingSpan
        elements := [namedTypeTraceValue (tracedQualifiedName name []) none]
      } { input with cursor := input.cursor + 4, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .dot) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (comma.token_unique other)
    cases impossible
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .less) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (comma.token_unique other)
    cases impossible
  have child := checked_name_type (input := { input with cursor := input.cursor + 1 })
    nameAt nameTrace noDot noArgs notComptime notMapping
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := input) ⟨opening, rfl⟩
  have first : ({ input with cursor := input.cursor + 1 } : State).peek? =
      some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, nameAt.1, if_true, nameAt.2]
  have noClose : isSymbol { input with cursor := input.cursor + 1 } .rightParen = false := by
    simp only [isSymbol, State.peekKind?, first, Option.map_some]
    rfl
  have progress : input.cursor + 1 + 1 > input.cursor + 1 := by omega
  have tail := trailing_close_bypasses_any_child typeExpr
    { span := openingSpan, value := .symbol .leftParen } .rightParen .typeExpr .typeExpr
    ({ input with cursor := input.cursor + 1 } : State).remainingCount
    [namedTypeTraceValue (tracedQualifiedName name []) none]
    (input := { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev })
    (commaSpan := commaSpan) (closingSpan := closingSpan)
    ⟨comma, rfl⟩ ⟨closing, rfl⟩
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noClose,
    Bool.false_eq_true, if_false, child, progress, if_true]
  exact tail

theorem checked_type_list_missing_separator
    {input : State} {name : Identifier} {trace : List ParseDiagnostic}
    {openingSpan badSpan : SourceSpan}
    (opening : TokenAt input.tokens input.window.endIndex input.cursor
      { span := openingSpan, value := .symbol .leftParen })
    (nameAt : TokenAt input.tokens input.window.endIndex (input.cursor + 1)
      { span := name.span, value := .identifier name.value })
    (bad : TokenAt input.tokens input.window.endIndex (input.cursor + 2)
      { span := badSpan, value := .symbol .plus })
    (nameTrace : IdentifierDiagnosticTrace name trace)
    (notComptime : name.value ≠ ContextualKeyword.comptime.spelling)
    (notMapping : name.value ≠ ContextualKeyword.mapping.spelling) :
    delimited .leftParen .rightParen true typeExpr .typeExpr .typeExpr input =
      .reject {
        span := badSpan, found := some (.symbol .plus)
        expected := { head := .symbol .comma, tail := [.symbol .rightParen] }
        context := .typeExpr
      } { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev } := by
  have noDot : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .dot) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (bad.token_unique other)
    cases impossible
  have noArgs : TokenKindAbsentAt input.tokens input.window.endIndex (input.cursor + 2) (.symbol .less) := by
    rintro ⟨span, other⟩
    have impossible := congrArg (·.value) (bad.token_unique other)
    cases impossible
  have child := checked_name_type (input := { input with cursor := input.cursor + 1 })
    nameAt nameTrace noDot noArgs notComptime notMapping
  have marker := symbol_eq_ok_of_exactTokenParses .leftParen .typeExpr
    (input := input) ⟨opening, rfl⟩
  have first : ({ input with cursor := input.cursor + 1 } : State).peek? =
      some { span := name.span, value := .identifier name.value } := by
    simp only [State.peek?, nameAt.1, if_true, nameAt.2]
  have noClose : isSymbol { input with cursor := input.cursor + 1 } .rightParen = false := by
    simp only [isSymbol, State.peekKind?, first, Option.map_some]
    rfl
  let next : State := { input with cursor := input.cursor + 2, diagnosticsRev := trace.reverse ++ input.diagnosticsRev }
  have nextFound : next.peek? = some { span := badSpan, value := .symbol .plus } := by
    simp only [next, State.peek?, bad.1, if_true, bad.2]
  have noComma : isSymbol next .comma = false := by
    simp only [isSymbol, State.peekKind?, nextFound, Option.map_some]
    rfl
  have noFinish : isSymbol next .rightParen = false := by
    simp only [isSymbol, State.peekKind?, nextFound, Option.map_some]
    rfl
  have progress : input.cursor + 1 + 1 > input.cursor + 1 := by omega
  simp only [delimited, delimitedWithPolicy, marker, Bool.true_and, noClose,
    Bool.false_eq_true, if_false, child, progress, if_true]
  change afterDelimitedElement typeExpr .rightParen true .typeExpr .typeExpr
    { span := openingSpan, value := .symbol .leftParen }
    (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1) [_] next = _
  simp only [afterDelimitedElement, noComma, noFinish, Bool.false_eq_true, if_false]
  simp only [rejectAt, State.currentSpan, State.peekKind?, nextFound, Option.map_some]
  rfl

end Solcore.Test.SyntaxCheckedTypeListTraceSupport
end

section
-- leanmerge: from Solcore.Test.SyntaxConcreteTypeExpressionTraceProperties
/-! Concrete type-bearing expression fragments execute directly from the
independent recursive child derivation, without child parser contracts. Marker
tokens add no events; normalization keeps the child's entire ordered suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxConcreteTypeExpressionTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem protected_suffix (input : State) (lexical : List LexicalDiagnostic)
    {trace : List ParseDiagnostic}
    (childProtected : ParseDiagnosticCascadeFilters input.file.content (lexical.map (·.span)) trace trace) :
    filterParseDiagnostics input.file lexical (input.diagnostics ++ trace) =
      filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics input.file lexical input.diagnostics ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters input.file lexical childProtected)

theorem proxy_executes_independent_type
    {input : State} {afterMarker after : Remainder} {markerSpan : SourceSpan}
    {type : TypeExpr} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.symbol .at) input.declarativeRemainder markerSpan afterMarker)
    (typed : TypeExprTraceParses input.file.id input.window.endByte afterMarker type after trace)
    (lexical : List LexicalDiagnostic) :
    ∃ output, proxyExpression input = .ok
        { span := SourceSpan.cover markerSpan type.span, value := .proxy markerSpan type } output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical output.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases proxyExpression_concrete_trace_success_iff.mp (.parsed markerSpan marker typed) with
    ⟨output, result, afterEq, events⟩
  refine ⟨output, result, afterEq, events, ?_⟩
  rw [events]
  exact protected_suffix input lexical (typed.cascadeFilters _ _)

theorem proxy_keeps_complete_type_failure
    {input : State} {afterMarker after : Remainder} {markerSpan : SourceSpan}
    {failure : Failure} {trace : List ParseDiagnostic}
    (marker : ExactTokenParses (.symbol .at) input.declarativeRemainder markerSpan afterMarker)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      afterMarker after failure.toDiagnostic trace) (lexical : List LexicalDiagnostic) :
    ∃ rejected, proxyExpression input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical rejected.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases proxyExpression_concrete_trace_reject_failure_iff.mp (.typeRejected markerSpan marker rejection) with
    ⟨rejected, result, afterEq, events⟩
  refine ⟨rejected, result, afterEq, events, ?_⟩
  rw [events]
  exact protected_suffix input lexical (rejection.cascadeFilters _ _)

theorem return_annotation_executes_independent_type
    {input : State} {afterArrow after : Remainder} {arrowSpan : SourceSpan}
    {type : TypeExpr} {trace : List ParseDiagnostic}
    (arrow : ExactTokenParses (.symbol .arrow) input.declarativeRemainder arrowSpan afterArrow)
    (typed : TypeExprTraceParses input.file.id input.window.endByte afterArrow type after trace)
    (lexical : List LexicalDiagnostic) :
    ∃ output, optionalLambdaReturnType input = .ok (some type) output ∧
      output.declarativeRemainder = after ∧ output.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical output.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases optionalLambdaReturnType_concrete_trace_success_iff.mp (.present arrowSpan arrow typed) with
    ⟨output, result, afterEq, events⟩
  refine ⟨output, result, afterEq, events, ?_⟩
  rw [events]
  exact protected_suffix input lexical (typed.cascadeFilters _ _)

theorem return_annotation_keeps_complete_type_failure
    {input : State} {afterArrow after : Remainder} {arrowSpan : SourceSpan}
    {failure : Failure} {trace : List ParseDiagnostic}
    (arrow : ExactTokenParses (.symbol .arrow) input.declarativeRemainder arrowSpan afterArrow)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      afterArrow after failure.toDiagnostic trace) (lexical : List LexicalDiagnostic) :
    ∃ rejected, optionalLambdaReturnType input = .reject failure rejected ∧
      rejected.declarativeRemainder = after ∧ rejected.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical rejected.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases optionalLambdaReturnType_concrete_trace_reject_failure_iff.mp (.typeRejected arrowSpan arrow rejection) with
    ⟨rejected, result, afterEq, events⟩
  refine ⟨rejected, result, afterEq, events, ?_⟩
  rw [events]
  exact protected_suffix input lexical (rejection.cascadeFilters _ _)

end Solcore.Test.SyntaxConcreteTypeExpressionTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxMappingTypeTraceProperties
/-! Raw prefix failures bypass all children, while a missing closing delimiter
preserves both completed children and their exact state. The protected suffix
includes all repeated events, but not the separate uncommitted failure report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxMappingTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem missing_marker_bypasses_every_child (nested : Parser TypeExpr)
    {input : State} {failure : Failure}
    (absent : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor
      (.identifier ContextualKeyword.mapping.spelling))
    (reported : RejectAtReports input.file.id input.window.endByte { head := .contextual .mapping, tail := [] }
      .typeExpr input.declarativeRemainder failure.toDiagnostic) :
    parseMappingType nested input = .reject failure input := by
  rcases (contextual_reject_reports_iff .mapping .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseMappingType, bind, result]

theorem missing_opening_bypasses_every_child (nested : Parser TypeExpr)
    {input afterMarker : State} {marker : Token} {failure : Failure}
    (markerResult : contextual .mapping .typeExpr input = .ok marker afterMarker)
    (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.window.endIndex afterMarker.cursor (.symbol .leftParen))
    (reported : RejectAtReports afterMarker.file.id afterMarker.window.endByte
      { head := .symbol .leftParen, tail := [] } .typeExpr afterMarker.declarativeRemainder failure.toDiagnostic) :
    parseMappingType nested input = .reject failure afterMarker := by
  rcases (symbol_reject_reports_iff .leftParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  simp only [parseMappingType, bind, markerResult, result]

theorem missing_closing_keeps_both_child_states_and_events (nested : Parser TypeExpr)
    {input afterMarker afterOpening afterKey afterArrow afterValue : State}
    {marker opening arrow : Token} {key value : TypeExpr} {failure : Failure}
    {keyEvents valueEvents : List ParseDiagnostic}
    (markerResult : contextual .mapping .typeExpr input = .ok marker afterMarker)
    (openingResult : symbol .leftParen .typeExpr afterMarker = .ok opening afterOpening)
    (keyResult : nested afterOpening = .ok key afterKey)
    (arrowResult : symbol .fatArrow .typeExpr afterKey = .ok arrow afterArrow)
    (valueResult : nested afterArrow = .ok value afterValue)
    (absent : TokenKindAbsentAt afterValue.tokens afterValue.window.endIndex afterValue.cursor (.symbol .rightParen))
    (reported : RejectAtReports afterValue.file.id afterValue.window.endByte
      { head := .symbol .rightParen, tail := [] } .typeExpr afterValue.declarativeRemainder failure.toDiagnostic)
    (keyEq : afterKey.diagnostics = input.diagnostics ++ keyEvents)
    (valueEq : afterValue.diagnostics = afterKey.diagnostics ++ valueEvents) :
    parseMappingType nested input = .reject failure afterValue ∧
      afterValue.diagnostics = input.diagnostics ++ keyEvents ++ valueEvents := by
  rcases (symbol_reject_reports_iff .rightParen .typeExpr).mp ⟨absent, reported⟩ with ⟨actual, result, reportEq⟩
  cases Failure.toDiagnostic_injective reportEq
  refine ⟨?_, by rw [valueEq, keyEq]⟩
  simp only [parseMappingType, bind, markerResult, openingResult, keyResult, arrowResult, valueResult, result]

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_mapping_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : MappingTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_mapping_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : MappingTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxMappingTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedTypeFinishingTraceProperties
/-! Bare, qualified, and other names take distinct diagnostic branches. The
full named range includes any arguments; normalization keeps the full fresh
constraint event even when earlier diagnostics already contain duplicates. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedTypeFinishingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem bare_mapping_reports_full_named_span (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments)
      (input.emit {
        span := (namedTypeTraceValue name arguments).span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }) :=
  finishNamedType_eq_ok_of_trace name arguments input (.canonicalRequired ⟨bare, spelling⟩)

theorem mapping_arguments_extend_diagnostic_span (name : QualifiedName)
    (arguments : NonemptyDelimitedList TypeExpr) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    finishNamedType name (some arguments) input = .ok (namedTypeTraceValue name (some arguments))
      (input.emit {
        span := SourceSpan.cover name.span arguments.span
        kind := .constraintViolation .mappingRequiresCanonicalForm
      }) :=
  bare_mapping_reports_full_named_span name (some arguments) input bare spelling

theorem qualified_mapping_is_silent (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (qualified : name.value.components.tail ≠ []) :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments) input :=
  finishNamedType_eq_ok_of_trace name arguments input (.ordinary (fun spelling => qualified spelling.1))

theorem other_spelling_is_silent (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (other : name.value.components.head.value ≠ "mapping") :
    finishNamedType name arguments input = .ok (namedTypeTraceValue name arguments) input :=
  finishNamedType_eq_ok_of_trace name arguments input (.ordinary (fun spelling => other spelling.2))

theorem repeated_prior_mapping_reports_are_retained (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) (input : State)
    (bare : name.value.components.tail = []) (spelling : name.value.components.head.value = "mapping") :
    let report : ParseDiagnostic := {
      span := (namedTypeTraceValue name arguments).span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }
    ∃ output, finishNamedType name arguments { input with diagnosticsRev := [report, report] } =
        .ok (namedTypeTraceValue name arguments) output ∧ output.diagnostics = [report, report, report] := by
  dsimp only
  exact ⟨_, bare_mapping_reports_full_named_span name arguments _ bare spelling, rfl⟩

theorem named_type_reports_survive_normalization
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {name : QualifiedName} {arguments : Option (NonemptyDelimitedList TypeExpr)}
    {trace : List ParseDiagnostic} (events : NamedTypeFinishingTrace name arguments trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical (events.cascadeFilters _ _)

end Solcore.Test.SyntaxNamedTypeFinishingTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxNamedTypeTraceProperties
/-! Complete raw named-type consumers separate the final spelling constraint
from argument failure. They preserve arbitrary intermediate states/events and
do not assume recursive type execution or dispatcher selection. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxNamedTypeTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem no_arguments_bypass_any_child (nested : Parser TypeExpr)
    {input afterName : State} {name : QualifiedName} {trace : List ParseDiagnostic}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (absent : TokenKindAbsentAt afterName.tokens afterName.window.endIndex afterName.cursor (.symbol .less))
    (finished : NamedTypeFinishingTrace name none trace) :
    parseNamedType nested input = .ok (namedTypeTraceValue name none)
      { afterName with diagnosticsRev := trace.reverse ++ afterName.diagnosticsRev } :=
  parseNamedType_success_iff_components.mpr ⟨name, afterName, none, afterName,
    nameResult, parseNamedTypeArguments_eq_none_of_absent nested absent,
    finishNamedType_eq_ok_of_trace name none afterName finished⟩

theorem mapping_constraint_follows_all_argument_events (nested : Parser TypeExpr)
    {input afterName afterArguments : State} {name : QualifiedName}
    {arguments : NonemptyDelimitedList TypeExpr} {nameEvents argumentEvents : List ParseDiagnostic}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (argumentsResult : parseNamedTypeArguments nested afterName = .ok (some arguments) afterArguments)
    (spelling : UnqualifiedMappingSpelling name)
    (nameEq : afterName.diagnostics = input.diagnostics ++ nameEvents)
    (argumentsEq : afterArguments.diagnostics = afterName.diagnostics ++ argumentEvents) :
    ∃ output, parseNamedType nested input = .ok (namedTypeTraceValue name (some arguments)) output ∧
      output = { afterArguments with diagnosticsRev := {
        span := (namedTypeTraceValue name (some arguments)).span
        kind := .constraintViolation .mappingRequiresCanonicalForm } :: afterArguments.diagnosticsRev } ∧
      output.diagnostics = input.diagnostics ++ nameEvents ++ argumentEvents ++ [{
        span := (namedTypeTraceValue name (some arguments)).span
        kind := .constraintViolation .mappingRequiresCanonicalForm }] := by
  refine ⟨_, parseNamedType_success_iff_components.mpr ⟨name, afterName, some arguments, afterArguments,
    nameResult, argumentsResult,
    finishNamedType_eq_ok_of_trace name (some arguments) afterArguments (.canonicalRequired spelling)⟩, rfl, ?_⟩
  simp only [State.diagnostics, List.reverse_append, List.reverse_reverse]
  change afterArguments.diagnostics ++ [_] = _
  rw [argumentsEq, nameEq]
  rfl

theorem argument_failure_bypasses_finishing (nested : Parser TypeExpr)
    {input afterName rejected : State} {name : QualifiedName} {failure : Failure}
    (nameResult : qualifiedName .typeExpr .typeExpr input = .ok name afterName)
    (argumentsResult : parseNamedTypeArguments nested afterName = .reject failure rejected) :
    parseNamedType nested input = .reject failure rejected :=
  parseNamedType_reject_iff_components.mpr (.inr ⟨name, afterName, nameResult, argumentsResult⟩)

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem successful_named_type_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : NamedTypeTraceParses elementTrace source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters childProtected))

theorem rejected_named_type_keeps_protected_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    (childProtected : ∀ {input value output trace}, elementTrace source endByte input value output trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    (rejectedProtected : ∀ {input output report trace}, elementRejects source endByte input output report trace →
      ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
    {input output : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NamedTypeTraceRejects elementTrace elementRejects source endByte input output report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters childProtected rejectedProtected))

end Solcore.Test.SyntaxNamedTypeTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserGenericParameterProperties
/-! External consumers for generic-parameter provenance and shape laws. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @NonemptyList.ValidFor
example := @NonemptyDelimitedList.ValidFor
example := @Option.ValidFor

example : genericParameters.ValidFor
    (NonemptyDelimitedList.ValidFor Located.ValidFor) :=
  genericParameters_validFor

example : Parser.PreservesTokensOnSuccess genericParameters :=
  genericParameters_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess genericParameters :=
  genericParameters_cursorMonotoneOnSuccess

example : optionalGenericParameters.ValidFor
    (Option.ValidFor
      (NonemptyDelimitedList.ValidFor Located.ValidFor)) :=
  optionalGenericParameters_validFor

example : Parser.PreservesTokensOnSuccess optionalGenericParameters :=
  optionalGenericParameters_preservesTokensOnSuccess

example : Parser.CursorMonotoneOnSuccess optionalGenericParameters :=
  optionalGenericParameters_cursorMonotoneOnSuccess

example (file : SourceFile) (values : GenericParameters)
    (valid : NonemptyDelimitedList.ValidFor Located.ValidFor file values) :
    values.span.ValidFor file ∧
      values.elements.head.span.ValidFor file := by
  refine ⟨valid.1, valid.2 values.elements.head ?_⟩
  simp [NonemptyList.toList]

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserGenericParametersSoundnessProperties
/-! External consumers for exact generic-parameter outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserGenericParametersSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @GenericParametersParses
example := @GenericParametersRejects
example := @genericParametersDeterministicOutcomeSpec
example := @genericParametersExactOutcomeSpec
example := @OptionalGenericParametersParses
example := @OptionalGenericParametersRejects
example := @optionalGenericParametersDeterministicOutcomeSpec
example := @optionalGenericParametersExactOutcomeSpec
example := @requireGenericParameters_success_shape
example := @genericParameters_success_sound
example := @genericParameters_success_sound_and_validFor
example := @optionalGenericParameters_success_sound
example := @optionalGenericParameters_success_sound_and_validFor
example := @genericParameters_reject_sound
example := @genericParameters_ordinaryOutcome_sound
example := @genericParameters_exactOutcomeSpec
example := @genericParameters_success_result_unique
example := @genericParameters_reject_output_unique
example := @optionalGenericParameters_reject_sound
example := @optionalGenericParameters_ordinaryOutcome_sound
example := @optionalGenericParameters_exactOutcomeSpec
example := @optionalGenericParameters_success_result_unique
example := @optionalGenericParameters_reject_output_unique

example {input next : State} {parameters : GenericParameters}
    (result : genericParameters input = .ok parameters next) :
    GenericParametersParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  genericParameters_success_sound result

example {input next : State} {parameters : Option GenericParameters}
    (result : optionalGenericParameters input = .ok parameters next) :
    OptionalGenericParametersParses input.declarativeRemainder parameters
      next.declarativeRemainder :=
  optionalGenericParameters_success_sound result

example {input rejected : State} {failure : Failure}
    (result : genericParameters input = .reject failure rejected) :
    GenericParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  genericParameters_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : optionalGenericParameters input = .reject failure rejected) :
    OptionalGenericParametersRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  optionalGenericParameters_reject_sound result

end Solcore.Test.SyntaxParserGenericParametersSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserGenericParametersTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserGenericParametersTotalityProperties

open Solcore.Syntax.Parser

example := @genericParameters_ordinary
example := @genericParameters_invariantFreeOnValid
example := @genericParameters_ne_invariant
example := @optionalGenericParameters_ordinary
example := @optionalGenericParameters_invariantFreeOnValid
example := @optionalGenericParameters_ne_invariant

end Solcore.Test.SyntaxParserGenericParametersTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPredicateProperties
/-! External compile consumers for canonical predicate contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := predicate_validFor
example := predicate_preservesTokenWindow
example := predicate_preservesTokensOnSuccess
example := predicate_cursorMonotoneOnSuccess
example := predicate_startsAtCurrentTokenOnSuccess
example := PredicateInternals.barePredicates_validFor
example := PredicateInternals.barePredicates_preservesTokenWindow
example := PredicateInternals.barePredicates_preservesTokensOnSuccess
example := PredicateInternals.barePredicates_cursorMonotoneOnSuccess
example := PredicateInternals.groupedPredicates_validFor
example := PredicateInternals.groupedPredicates_preservesTokenWindow
example := PredicateInternals.groupedPredicates_preservesTokensOnSuccess
example := PredicateInternals.groupedPredicates_cursorMonotoneOnSuccess
example := PredicateInternals.predicateSequence_validFor
example := PredicateInternals.predicateSequence_preservesTokenWindow
example := PredicateInternals.predicateSequence_preservesTokensOnSuccess
example := PredicateInternals.predicateSequence_cursorMonotoneOnSuccess
example := PredicateInternals.barePredicates_startsAtCurrentTokenOnSuccess
example := PredicateInternals.groupedPredicates_startsAtCurrentTokenOnSuccess
example := PredicateInternals.predicateSequence_startsAtCurrentTokenOnSuccess
example := whereClause_validFor
example := whereClause_preservesTokenWindow
example := whereClause_preservesTokensOnSuccess
example := whereClause_cursorMonotoneOnSuccess
example := @whereClause_some_startsAtCurrentTokenOnSuccess

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPredicateSequenceTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateSequenceTotalityProperties

open Solcore.Syntax.Parser

example := @predicate_invariantFreeOnValid
example := @predicate_ordinary
example := @predicate_elementTotalityContract
example := @PredicateInternals.barePredicatesTail_ordinary_of_remainingCount_lt
example := @PredicateInternals.barePredicatesTail_ne_invariant_of_remainingCount_lt
example := @PredicateInternals.barePredicatesTail_production_ordinary
example := @PredicateInternals.barePredicates_ordinary
example := @PredicateInternals.barePredicates_invariantFreeOnValid
example := @PredicateInternals.groupedPredicates_ordinary
example := @PredicateInternals.groupedPredicates_invariantFreeOnValid
example := @PredicateInternals.predicateSequence_ordinary
example := @PredicateInternals.predicateSequence_invariantFreeOnValid

end Solcore.Test.SyntaxParserPredicateSequenceTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPredicateSoundnessProperties
/-! External consumers for trait-predicate grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @PredicateParses
example := @PredicateRejects
example := @predicateDeterministicOutcomeSpec
example := @predicateExactOutcomeSpec
example := @predicate_success_sound
example := @predicate_success_sound_and_validFor
example := @predicate_reject_sound
example := @predicate_ordinaryOutcome_sound
example := @predicate_exactOutcomeSpec
example := @predicate_success_result_unique
example := @predicate_reject_output_unique

example {input next : State} {value : Predicate}
    (result : predicate input = .ok value next) :
    PredicateParses input.declarativeRemainder value
      next.declarativeRemainder :=
  predicate_success_sound result

example {input next : State} {value : Predicate}
    (inputValid : input.ValidFor)
    (result : predicate input = .ok value next) :
    PredicateParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  predicate_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : predicate input = .reject failure rejected) :
    PredicateRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  predicate_reject_sound result

example :
    DeterministicOutcomeSpec PredicateParses PredicateRejects :=
  predicateDeterministicOutcomeSpec

end Solcore.Test.SyntaxParserPredicateSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserPredicateTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateTotalityProperties

open Solcore.Syntax.Parser

example := @predicate_invariantFreeOnValid
example := @predicate_ne_invariant
example := @predicate_elementTotalityContract

end Solcore.Test.SyntaxParserPredicateTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserQualifiedNameInternals
/-! External consumers for proof-visible qualified-name components. -/

namespace Tests

open Solcore.Syntax.Parser

example := @QualifiedNameInternals.finishQualifiedName
example := @QualifiedNameInternals.qualifiedNameTail

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserQualifiedNameSoundnessProperties
/-! External consumers for canonical qualified-name success soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserQualifiedNameSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TokenKindAbsentAt
example := @finalIdentifier
example := @DottedIdentifierTailParses
example := @QualifiedNameParses
example := @symbolAbsentAt_of_isSymbol_eq_false
example := @qualifiedName_success_sound
example := @qualifiedName_success_sound_and_validFor

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedNameParses input.declarativeRemainder name
      next.declarativeRemainder :=
  qualifiedName_success_sound context phase result

example (context : ParseContext) (phase : ParserPhase)
    {input next : State} {name : QualifiedName}
    (inputValid : input.ValidFor)
    (result : qualifiedName context phase input = .ok name next) :
    QualifiedNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file :=
  qualifiedName_success_sound_and_validFor context phase inputValid result

end Solcore.Test.SyntaxParserQualifiedNameSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserQualifiedNameTotalityProperties
/-! External consumers for qualified-name totality. -/

namespace Tests

open Solcore.Syntax.Parser

example :=
  @QualifiedNameInternals.qualifiedNameTail_ordinary_of_remainingCount_lt
example :=
  @QualifiedNameInternals.qualifiedNameTail_ne_invariant_of_remainingCount_lt
example := @QualifiedNameInternals.qualifiedNameTail_production_ordinary
example := @qualifiedName_ordinary
example := @qualifiedName_ne_invariant
example := @qualifiedName_elementTotalityContract

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeExprProperties
/-! External consumers for recursive type-expression and tuple contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @TypeExpr.ValidFor

example (nested : Parser TypeExpr)
    (valid : nested.ValidFor TypeExpr.ValidFor)
    (tokens : Parser.PreservesTokensOnSuccess nested) :
    (parseNamedType nested).ValidFor TypeExpr.ValidFor :=
  parseNamedType_validFor nested valid tokens

example (nested : Parser TypeExpr)
    (tokens : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedTypeArguments nested) :=
  parseNamedTypeArguments_preservesTokensOnSuccess nested tokens

example (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedTypeArguments nested) :=
  parseNamedTypeArguments_cursorMonotoneOnSuccess nested

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedTypeArguments nested) :=
  parseNamedTypeArguments_preservesTokenWindow nested window

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseNamedType nested) :=
  parseNamedType_preservesTokenWindow nested window

example (nested : Parser TypeExpr)
    (tokens : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseNamedType nested) :=
  parseNamedType_preservesTokensOnSuccess nested tokens

example (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseNamedType nested) :=
  parseNamedType_cursorMonotoneOnSuccess nested

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess (parseNamedType nested) (·.span) :=
  parseNamedType_startsAtCurrentTokenOnSuccess nested

example := @typeExprWithFuel_validFor
example := @typeExprWithFuel_preservesTokenWindow
example := @typeExprWithFuel_preservesTokensOnSuccess
example := @typeExprWithFuel_cursorMonotoneOnSuccess
example := @typeExprWithFuel_startsAtCurrentTokenOnSuccess

example : typeExpr.ValidFor TypeExpr.ValidFor := typeExpr_validFor
example : Parser.PreservesTokenWindow typeExpr :=
  typeExpr_preservesTokenWindow
example : Parser.PreservesTokensOnSuccess typeExpr :=
  typeExpr_preservesTokensOnSuccess
example : Parser.CursorMonotoneOnSuccess typeExpr :=
  typeExpr_cursorMonotoneOnSuccess
example : Parser.StartsAtCurrentTokenOnSuccess typeExpr (·.span) :=
  typeExpr_startsAtCurrentTokenOnSuccess

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseMappingType nested).ValidFor TypeExpr.ValidFor :=
  parseMappingType_validFor nested nestedValid nestedStarts
    nestedPreserves nestedMonotone

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseMappingType nested) :=
  parseMappingType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseMappingType nested) :=
  parseMappingType_preservesTokenWindow nested window

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseMappingType nested) :=
  parseMappingType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseMappingType nested) (·.span) :=
  parseMappingType_startsAtCurrentTokenOnSuccess nested

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span))
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    (parseComptimeType nested).ValidFor TypeExpr.ValidFor :=
  parseComptimeType_validFor nested nestedValid nestedStarts
    nestedPreserves nestedMonotone

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseComptimeType nested) :=
  parseComptimeType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseComptimeType nested) :=
  parseComptimeType_preservesTokenWindow nested window

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseComptimeType nested) :=
  parseComptimeType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseComptimeType nested) (·.span) :=
  parseComptimeType_startsAtCurrentTokenOnSuccess nested

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseFunctionType nested).ValidFor TypeExpr.ValidFor :=
      parseFunctionType_validFor nested nestedValid nestedPreserves

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseFunctionType nested) :=
      parseFunctionType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseFunctionType nested) :=
  parseFunctionType_preservesTokenWindow nested window

example (nested : Parser TypeExpr) : Parser.CursorMonotoneOnSuccess
    (parseFunctionType nested) := parseFunctionType_cursorMonotoneOnSuccess nested

example (nested : Parser TypeExpr) : Parser.StartsAtCurrentTokenOnSuccess
    (parseFunctionType nested) (·.span) := parseFunctionType_startsAtCurrentTokenOnSuccess nested

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    (parseTupleType nested).ValidFor TypeExpr.ValidFor :=
  parseTupleType_validFor nested nestedValid nestedPreserves

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseTupleType nested) :=
  parseTupleType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseTupleType nested) :=
  parseTupleType_preservesTokenWindow nested window

example (nested : Parser TypeExpr) :
    Parser.CursorMonotoneOnSuccess (parseTupleType nested) :=
  parseTupleType_cursorMonotoneOnSuccess nested

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess
      (parseTupleType nested) (·.span) :=
  parseTupleType_startsAtCurrentTokenOnSuccess nested

example {file : SourceFile} {span : SourceSpan} {elements : List TypeExpr}
    (spanValid : span.ValidFor file)
    (elementsValid : ∀ element ∈ elements,
      TypeExpr.ValidFor file element) :
    TypeExpr.ValidFor file { span, value := .tuple elements } :=
  .tuple spanValid elementsValid

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeExprSoundnessProperties
/-! External consumers for recursive type-expression grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeExprSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TypeExprParses
example := @TypeExprTrailingDelimitedTailParses
example := @TypeExprTrailingDelimitedListParses
example := @OptionalNamedTypeArgumentsParses
example := @OptionalFunctionTypeReturnsParses
example := @DottedIdentifierTailParses.value_unique
example := @QualifiedNameParses.value_unique
example := @QualifiedNameParses.result_unique
example := @TypeQualifiedNameTailRejects.output_unique
example := @TypeQualifiedNameRejects.output_unique
example := @typeQualifiedNameExactOutcomeSpec
example := @FunctionTypeReturnsRejects.output_unique
example := @FunctionTypeRejects.output_unique
example := @ComptimeTypeRejects.output_unique
example := @MappingTypeRejects.output_unique
example := @ProxyTypeRejects.output_unique
example := @TupleTypeRejects.output_unique
example := @NamedTypeArgumentsRejects.output_unique
example := @NamedTypeRejects.output_unique
example := @TypeExprCoreRejects.output_unique
example := @TypeExprParses.value_unique
example := @TypeExprParses.result_unique
example := @TypeExprTrailingDelimitedTailParses.value_unique
example := @TypeExprTrailingDelimitedTailParses.result_unique
example := @TypeExprTrailingDelimitedListParses.value_unique
example := @TypeExprTrailingDelimitedListParses.result_unique
example := @OptionalNamedTypeArgumentsParses.value_unique
example := @OptionalNamedTypeArgumentsParses.result_unique
example := @OptionalFunctionTypeReturnsParses.value_unique
example := @OptionalFunctionTypeReturnsParses.result_unique
example := @typeExprExactOutcomeSpecWithFuel
example := @TypeExprRejects.output_unique
example := @typeExprExactOutcomeSpec
example := @typeExprWithFuel_success_sound
example := @typeExpr_success_sound
example := @typeExpr_success_sound_and_validFor
example := @typeExprWithFuel_exactOutcomeSpec
example := @typeExprWithFuel_success_result_unique
example := @typeExprWithFuel_reject_output_unique
example := @typeExpr_exactOutcomeSpec
example := @typeExpr_success_result_unique
example := @typeExpr_reject_output_unique

example {input next : State} {value : TypeExpr}
    (result : typeExpr input = .ok value next) :
    TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder :=
  typeExpr_success_sound result

example {input next : State} {value : TypeExpr}
    (inputValid : input.ValidFor)
    (result : typeExpr input = .ok value next) :
    TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  typeExpr_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserTypeExprSoundnessProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @typeExprWithFuel_ordinary_of_remainingCount_lt
example := @typeExprWithFuel_ne_invariant_of_remainingCount_lt
example := @typeExpr_invariantFreeOnValid
example := @typeExpr_ne_invariant
example := @typeExpr_elementTotalityContract

example : Parser.InvariantFreeOnValid typeExpr :=
  typeExpr_invariantFreeOnValid

end Solcore.Test.SyntaxParserTypeFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeFunctionFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFunctionFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example :=
  @TypeFunctionInternals.parseFunctionReturns_ordinary_of_elementFuel
example :=
  @TypeFunctionInternals.parseFunctionReturns_ne_invariant_of_elementFuel
example := @parseFunctionType_ordinary_of_elementFuel
example := @parseFunctionType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeFunctionFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeFunctionInternals
/-! External visibility checks for function-type parser components. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TypeFunctionInternals.parseFunctionReturns

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeFunctionTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeFunctionTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.Parser.TypeFunctionInternals

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionReturns nested) :=
  parseFunctionReturns_invariantFreeOnValid nested contract

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error :=
  parseFunctionType_ne_invariant nested contract input inputValid error

end Solcore.Test.SyntaxParserTypeFunctionTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeNamedFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeNamedFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseNamedTypeArguments_ordinary_of_elementFuel
example := @parseNamedTypeArguments_ne_invariant_of_elementFuel
example := @parseNamedType_ordinary_of_elementFuel
example := @parseNamedType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeNamedFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeNamedTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeNamedTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error :=
  parseNamedTypeArguments_ne_invariant nested contract input inputValid error

example (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) :=
  parseNamedType_ordinary nested contract input inputValid

end Solcore.Test.SyntaxParserTypeNamedTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeProxyProperties
/-! External consumers for proxy-type parser contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @Parser.StartsAtCurrentTokenOnSuccess
example := @Parser.bind_startsAtCurrentTokenOnSuccess_of_first
example := @Parser.orElse_startsAtCurrentTokenOnSuccess
example := @symbol_startsAtCurrentTokenOnSuccess
example := @TypeExpr.ValidFor.span_valid

example (nested : Parser TypeExpr)
    (nestedValid : nested.ValidFor TypeExpr.ValidFor)
    (nestedStarts : Parser.StartsAtCurrentTokenOnSuccess nested (·.span)) :
    (parseProxyType nested).ValidFor TypeExpr.ValidFor :=
  parseProxyType_validFor nested nestedValid nestedStarts

example (nested : Parser TypeExpr)
    (nestedPreserves : Parser.PreservesTokensOnSuccess nested) :
    Parser.PreservesTokensOnSuccess (parseProxyType nested) :=
  parseProxyType_preservesTokensOnSuccess nested nestedPreserves

example (nested : Parser TypeExpr)
    (window : Parser.PreservesTokenWindow nested) :
    Parser.PreservesTokenWindow (parseProxyType nested) :=
  parseProxyType_preservesTokenWindow nested window

example (nested : Parser TypeExpr)
    (nestedMonotone : Parser.CursorMonotoneOnSuccess nested) :
    Parser.CursorMonotoneOnSuccess (parseProxyType nested) :=
  parseProxyType_cursorMonotoneOnSuccess nested nestedMonotone

example (nested : Parser TypeExpr) :
    Parser.StartsAtCurrentTokenOnSuccess (parseProxyType nested) (·.span) :=
  parseProxyType_startsAtCurrentTokenOnSuccess nested

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeSimpleFuelTotalityProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeSimpleFuelTotalityProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseMappingType_ordinary_of_elementFuel
example := @parseMappingType_ne_invariant_of_elementFuel
example := @parseComptimeType_ordinary_of_elementFuel
example := @parseComptimeType_ne_invariant_of_elementFuel
example := @parseProxyType_ordinary_of_elementFuel
example := @parseProxyType_ne_invariant_of_elementFuel
example := @parseTupleType_ordinary_of_elementFuel
example := @parseTupleType_ne_invariant_of_elementFuel

end Solcore.Test.SyntaxParserTypeSimpleFuelTotalityProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeSimpleTotalityProperties
/-! External consumers for simple recursive type-form totality. -/

namespace Tests

open Solcore.Syntax.Parser

example := @parseMappingType_invariantFreeOnValid
example := @parseMappingType_ne_invariant
example := @parseComptimeType_invariantFreeOnValid
example := @parseComptimeType_ne_invariant
example := @parseProxyType_invariantFreeOnValid
example := @parseProxyType_ne_invariant
example := @parseTupleType_invariantFreeOnValid
example := @parseTupleType_ne_invariant

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypeStrictProperties
set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeStrictProperties

open Solcore.Syntax
open Solcore.Syntax.Parser

example := @parseNamedType_cursor_lt_onSuccess
example := @parseMappingType_cursor_lt_onSuccess
example := @parseComptimeType_cursor_lt_onSuccess
example := @parseProxyType_cursor_lt_onSuccess
example := @parseTupleType_cursor_lt_onSuccess
example := @parseFunctionType_cursor_lt_onSuccess
example := @typeExprWithFuel_cursor_lt_onSuccess
example := @typeExpr_cursor_lt_onSuccess

end Solcore.Test.SyntaxParserTypeStrictProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxParserTypes
/-! Successful canonical type-alias parser regressions. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax

private abbrev ByteRange := Nat × Nat

private inductive TypeShape where
  | named (components : List String) (arguments : Option (List TypeShape))
  | mapping (key value : TypeShape)
  | proxy (inner : TypeShape)
  | function
      (parameters : List TypeShape)
      (returns : Option (List TypeShape))
  | comptime (inner : TypeShape)
  | tuple (elements : List TypeShape)
  | error
  deriving Repr, BEq, Inhabited

private def parserSource : SourceId := {
  origin := .main
  path := "parser-types.sol"
}

private def assertEqual {alpha : Type} [BEq alpha] [Repr alpha]
    (actual expected : alpha) (label : String) : IO Unit := do
  unless actual == expected do
    throw (IO.userError
      s!"{label}: expected {reprStr expected}, got {reprStr actual}")

private def byteRange (span : SourceSpan) : ByteRange :=
  (span.startByte, span.endByte)

private partial def typeShape (type : TypeExpr) : TypeShape :=
  match type.value with
  | .named name arguments =>
      .named
        (name.value.components.toList.map (fun component => component.value))
        (arguments.map fun values =>
          values.elements.toList.map typeShape)
  | .mapping _ _ key value => .mapping (typeShape key) (typeShape value)
  | .proxy _ inner => .proxy (typeShape inner)
  | .function _ parameters returns =>
      .function (parameters.elements.map typeShape)
        (returns.map fun values => values.elements.map typeShape)
  | .comptime _ _ inner => .comptime (typeShape inner)
  | .tuple elements => .tuple (elements.map typeShape)
  | .error => .error

private def asTypeAlias? (item : TopItem) : Option TypeAliasDecl :=
  match item.value with
  | .typeAlias declaration => some declaration
  | _ => none

private def aliasDeclarations (label : String)
    (output : ParseOutput) : IO (List TypeAliasDecl) := do
  let declarations := output.parsed.items.filterMap asTypeAlias?
  assertEqual declarations.length output.parsed.items.length
    s!"{label} type-alias item count"
  pure declarations

private def declarationAt (label : String)
    (declarations : List TypeAliasDecl) (index : Nat) : IO TypeAliasDecl :=
  match declarations[index]? with
  | some declaration => pure declaration
  | none => throw (IO.userError s!"{label}: missing declaration {index}")

private def checkedParse (label content : String) : IO ParseOutput := do
  let file : SourceFile := { id := parserSource, content }
  match Parser.parse file with
  | .error error =>
      throw (IO.userError
        s!"{label}: parser invariant failed: {reprStr error}")
  | .ok output =>
      assertEqual output.parsed.source file.id s!"{label} source owner"
      assertEqual output.parsed.span (SourceSpan.fullFile file)
        s!"{label} full-file span"
      assertEqual output.lexicalDiagnostics []
        s!"{label} lexical diagnostics"
      unless output.parsed.items.all
          (fun item => item.span.isValidFor file) do
        throw (IO.userError s!"{label}: item span escaped the source")
      unless output.parseDiagnostics.all
          (fun diagnostic => diagnostic.span.isValidFor file) do
        throw (IO.userError s!"{label}: diagnostic span escaped the source")
      pure output

private def aliasNames (declarations : List TypeAliasDecl) : List String :=
  declarations.map fun declaration => declaration.value.name.value

private def aliasShapes
    (declarations : List TypeAliasDecl) : List TypeShape :=
  declarations.map fun declaration => typeShape declaration.value.value

private def aliasParameterNames
    (declaration : TypeAliasDecl) : Option (List String) :=
  declaration.value.parameters.map fun parameters =>
    parameters.elements.map (fun parameter => parameter.value)

private def named (name : String) : TypeShape :=
  .named [name] none

private def testEveryTypeForm : IO Unit := do
  let output ← checkedParse "all Core type forms" (String.intercalate "\n" [
    "type Plain = pkg.Word;",
    "type Generic = pkg.Box<A, mapping(K => @V)>;",
    "type Proxy = @Target;",
    "type Callable = function(A, @B) returns (C, ());",
    "type Compile = comptime<function()>;",
    "type EmptyTuple = ();",
    "type Singleton = (A);",
    "type Pair = (A, B);"
  ])
  assertEqual output.parseDiagnostics [] "all Core type-form diagnostics"
  let declarations ← aliasDeclarations "all Core type forms" output
  assertEqual (aliasNames declarations) [
      "Plain", "Generic", "Proxy", "Callable", "Compile",
      "EmptyTuple", "Singleton", "Pair"
    ] "all Core type-form names"
  assertEqual (aliasShapes declarations) [
      .named ["pkg", "Word"] none,
      .named ["pkg", "Box"] (some [
        named "A", .mapping (named "K") (.proxy (named "V"))]),
      .proxy (named "Target"),
      .function [named "A", .proxy (named "B")]
        (some [named "C", .tuple []]),
      .comptime (.function [] none),
      .tuple [],
      .tuple [named "A"],
      .tuple [named "A", named "B"]
    ] "all Core type-form source distinctions"

private def testAliasParameters : IO Unit := do
  let output ← checkedParse "alias parameters" (String.intercalate "\n" [
    "type NoParams = A;",
    "type EmptyParams() = B;",
    "type Explicit(T, U) = Pair<T, U>;"
  ])
  assertEqual output.parseDiagnostics [] "alias-parameter diagnostics"
  let declarations ← aliasDeclarations "alias parameters" output
  assertEqual (declarations.map aliasParameterNames)
    [none, some [], some ["T", "U"]]
    "absent, empty, and explicit alias parameters"

private def testContextualIdentifiers : IO Unit := do
  let output ← checkedParse "contextual identifiers"
    "type Contextual(comptime, derive, enum, from, hiding, impl, mapping, returns, trait, where, while) = while;"
  assertEqual output.parseDiagnostics [] "contextual-identifier diagnostics"
  let declarations ← aliasDeclarations "contextual identifiers" output
  let declaration ← declarationAt "contextual identifiers" declarations 0
  assertEqual (aliasParameterNames declaration) (some [
      "comptime", "derive", "enum", "from", "hiding", "impl",
      "mapping", "returns", "trait", "where", "while"
    ]) "contextual words in identifier positions"
  assertEqual (typeShape declaration.value.value) (named "while")
    "contextual word as named type"

private def testUtf8ByteSpans : IO Unit := do
  let output ← checkedParse "UTF-8 byte spans"
    "type 型(T) = comptime<λ.Word>;"
  assertEqual output.parseDiagnostics [] "UTF-8 span diagnostics"
  let declarations ← aliasDeclarations "UTF-8 byte spans" output
  let declaration ← declarationAt "UTF-8 byte spans" declarations 0
  assertEqual (byteRange declaration.span) (0, 32) "UTF-8 alias span"
  assertEqual (byteRange declaration.value.name.span) (5, 8)
    "UTF-8 alias-name span"
  match declaration.value.parameters with
  | some parameters =>
      assertEqual (byteRange parameters.span) (8, 11)
        "UTF-8 parameter delimiter span"
  | none => throw (IO.userError "UTF-8 parameters were lost")
  assertEqual (byteRange declaration.value.value.span) (14, 31)
    "UTF-8 comptime type span"
  match declaration.value.value.value with
  | .comptime keyword arguments inner =>
      assertEqual (byteRange keyword) (14, 22) "UTF-8 comptime keyword"
      assertEqual (byteRange arguments) (22, 31) "UTF-8 comptime arguments"
      assertEqual (byteRange inner.span) (23, 30) "UTF-8 inner type span"
      match inner.value with
      | .named name none =>
          assertEqual
            (name.value.components.toList.map fun component =>
              (component.value, byteRange component.span))
            [("λ", (23, 25)), ("Word", (26, 30))]
            "UTF-8 qualified-name component spans"
      | _ => throw (IO.userError "UTF-8 inner type changed shape")
  | _ => throw (IO.userError "UTF-8 outer type changed shape")

private def testMappingConstraint : IO Unit := do
  let output ← checkedParse "mapping canonical constraint"
    "type M = mapping<K, V>;"
  let declarations ← aliasDeclarations "mapping canonical constraint" output
  let declaration ← declarationAt "mapping canonical constraint" declarations 0
  assertEqual (typeShape declaration.value.value)
    (.named ["mapping"] (some [named "K", named "V"]))
    "noncanonical mapping remains source-shaped"
  assertEqual output.parseDiagnostics [{
      span := declaration.value.value.span
      kind := .constraintViolation .mappingRequiresCanonicalForm
    }] "mapping canonical constraint diagnostic"
  assertEqual (byteRange declaration.value.value.span) (9, 22)
    "mapping canonical constraint span"

private def testHyphenDiagnostic : IO Unit := do
  let output ← checkedParse "hyphen diagnostic"
    "type bad-name = Good;"
  let declarations ← aliasDeclarations "hyphen diagnostic" output
  let declaration ← declarationAt "hyphen diagnostic" declarations 0
  assertEqual declaration.value.name.value "bad-name"
    "hyphenated identifier preservation"
  assertEqual output.parseDiagnostics [{
      span := declaration.value.name.span
      kind := .invalidIdentifierHyphen "bad-name"
    }] "hyphen diagnostic"
  assertEqual (byteRange declaration.value.name.span) (5, 13)
    "hyphen diagnostic span"

/-- Run successful canonical type-alias parser and diagnostic regressions. -/
def testSyntaxParserTypes : IO Unit := do
  testEveryTypeForm
  testAliasParameters
  testContextualIdentifiers
  testUtf8ByteSpans
  testMappingConstraint
  testHyphenDiagnostic

end Tests
end

section
-- leanmerge: from Solcore.Test.SyntaxQualifiedNameSuccessTraceProperties
/-! Canonical checked qualified names retain forward components, each located
spelling event, arbitrary earlier events, and the unread following identifier. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxQualifiedNameSuccessTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "qualified-name-trace.sol" }
private def file : SourceFile := { id := source, content := "a-b.c-d.e-f tail" }
private def span (first last : Nat) : SourceSpan := { source, startByte := first, endByte := last }
private def nameA : Identifier := { span := span 0 3, value := "a-b" }
private def nameC : Identifier := { span := span 4 7, value := "c-d" }
private def nameE : Identifier := { span := span 8 11, value := "e-f" }
private def token (name : Identifier) : Token := { span := name.span, value := .identifier name.value }
private def hyphen (name : Identifier) : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def tokens : List Token := [token nameA, { span := span 3 4, value := .symbol .dot },
  token nameC, { span := span 7 8, value := .symbol .dot }, token nameE,
  { span := span 12 16, value := .identifier "tail" }]
private def lexed : LexedFile := { source, tokens, comments := [], diagnostics := [] }
private def remaining (cursor : Nat) : Remainder := { tokens := tokens.toArray, endIndex := 6, cursor }
private def value : QualifiedName := {
  span := span 0 11
  value := { components := { head := nameA, tail := [nameC, nameE] } }
}
private def events : List ParseDiagnostic := [hyphen nameA, hyphen nameC, hyphen nameE]

private theorem names_trace : QualifiedNameTraceParses source 16 (remaining 0) value (remaining 5) events := by
  have last : DottedIdentifierTailTraceParses source 16 (remaining 5) [] (remaining 5) [] :=
    .done (by simp [TokenKindAbsentAt, TokenAt, remaining, tokens])
  have second : DottedIdentifierTailTraceParses source 16 (remaining 3) [nameE] (remaining 5) [hyphen nameE] :=
    .next (span 7 8) (afterDot := remaining 4) (afterComponent := remaining 5)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameE; decide))) last
  have rest : DottedIdentifierTailTraceParses source 16 (remaining 1) [nameC, nameE]
      (remaining 5) [hyphen nameC, hyphen nameE] :=
    .next (span 3 4) (afterDot := remaining 2) (afterComponent := remaining 3)
      ⟨⟨by decide, rfl⟩, rfl⟩
      (.parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameC; decide))) second
  have first : IdentifierTraceParses (remaining 0) nameA (remaining 1) [hyphen nameA] :=
    .parsed ⟨⟨by decide, rfl⟩, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling nameA; decide))
  exact .parsed first rest

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem canonical_names_lex : Lexer.lex file = .ok lexed := by
  have checked : (Lexer.lex file).toOption = some lexed := by decide +kernel
  cases result : Lexer.lex file with
  | error error => simp only [result, Except.toOption] at checked; contradiction
  | ok actual => simp only [result, Except.toOption] at checked; cases checked; rfl

/-- Every context and phase use the same successful maximal checked path.
The exact output state retains all six tokens and the complete 16-byte window. -/
theorem canonical_names_success (context : ParseContext) (phase : ParserPhase)
    (prior : List ParseDiagnostic) :
    ∃ actualLexed output, Lexer.lex file = .ok actualLexed ∧
      qualifiedName context phase { State.initial file actualLexed with diagnosticsRev := prior.reverse } =
        .ok value output ∧ output.declarativeRemainder = remaining 5 ∧
      output.diagnostics = prior ++ events ∧ output.file = file ∧
      output.window = { endIndex := 6, endByte := 16 } ∧
      output.peek? = some { span := span 12 16, value := .identifier "tail" } := by
  let input : State := { State.initial file lexed with diagnosticsRev := prior.reverse }
  have parsed : QualifiedNameTraceParses input.file.id input.window.endByte input.declarativeRemainder
      value (remaining 5) events := names_trace
  have result := qualifiedName_eq_ok_of_trace context phase parsed
  refine ⟨lexed, _, canonical_names_lex, result, rfl, ?_, rfl, rfl, rfl⟩
  change (events.reverse ++ prior.reverse).reverse = prior ++ events
  simp only [List.reverse_append, List.reverse_reverse]

/-- An absent dot ends the tail without touching any part of the state,
including diagnostics and arbitrary first/last/reversed prefix accumulators. -/
theorem stopped_tail_keeps_arbitrary_accumulator (context : ParseContext) (phase : ParserPhase)
    (first last : Identifier) (tailRev : List Identifier) (input : State) (fuel : Nat)
    (noDot : TokenKindAbsentAt input.tokens input.window.endIndex input.cursor (.symbol .dot)) :
    QualifiedNameInternals.qualifiedNameTail context phase first (fuel + 1) last tailRev input =
      .ok (qualifiedNameFromSuffix first last tailRev.reverse []) input := by
  simp only [QualifiedNameInternals.qualifiedNameTail, DelimitedTraceInternals.symbol_absent .dot noDot,
    Bool.false_eq_true, if_false, QualifiedNameInternals.finishQualifiedName,
    qualifiedNameFromSuffix, finalIdentifier, List.append_nil]

theorem complete_name_events_survive_filtering (normalizationFile : SourceFile)
    (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic) :
    filterParseDiagnostics normalizationFile lexical (prior ++ events) =
      filterParseDiagnostics normalizationFile lexical prior ++ events := by
  rw [filterParseDiagnostics_append]
  exact congrArg (filterParseDiagnostics normalizationFile lexical prior ++ ·)
    (filterParseDiagnostics_eq_of_cascadeFilters normalizationFile lexical (names_trace.cascadeFilters _ _))

end Solcore.Test.SyntaxQualifiedNameSuccessTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeExprTraceOutcomeProperties
/-! Independent recursive uniqueness fixes every diagnostic event of an actual
execution and excludes an opposite declarative outcome. Valid-state reverse
correspondence is explicitly narrower than unrestricted soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceOutcomeProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem actual_success_fixes_every_claimed_trace
    {input output : State} {actual claimed : TypeExpr} {after : Remainder}
    {trace : List ParseDiagnostic} (result : typeExpr input = .ok actual output)
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder claimed after trace) :
    actual = claimed ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ rejected report events, TypeExprTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected report events := by
  rcases typeExpr_trace_success_sound result with ⟨actualTrace, actualParsed, events⟩
  rcases actualParsed.result_unique parsed with ⟨valueEq, afterEq, rfl⟩
  exact ⟨valueEq, afterEq, events, parsed.disjoint_rejection⟩

theorem actual_rejection_fixes_report_and_every_claimed_event
    {input rejected : State} {failure : Failure} {after : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (result : typeExpr input = .reject failure rejected)
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after report trace) :
    rejected.declarativeRemainder = after ∧ failure.toDiagnostic = report ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ value output events, TypeExprTraceParses input.file.id input.window.endByte
        input.declarativeRemainder value output events := by
  rcases typeExpr_reject_trace_sound result with ⟨actualTrace, actualRejected, events⟩
  rcases actualRejected.result_unique rejection with ⟨afterEq, reportEq, rfl⟩
  exact ⟨afterEq, reportEq, events, rejection.disjoint_success⟩

theorem valid_input_realizes_success_with_exact_events
    {input : State} (inputValid : input.ValidFor) {value : TypeExpr} {after : Remainder}
    {trace : List ParseDiagnostic}
    (parsed : TypeExprTraceParses input.file.id input.window.endByte
      input.declarativeRemainder value after trace) :
    ∃ output, typeExpr input = .ok value output ∧ output.declarativeRemainder = after ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ rejected report events, TypeExprTraceRejects input.file.id input.window.endByte
        input.declarativeRemainder rejected report events := by
  rcases (typeExpr_trace_success_iff_onValid inputValid).mp parsed with
    ⟨output, result, afterEq, events⟩
  exact ⟨output, result, afterEq, events, parsed.disjoint_rejection⟩

theorem valid_input_realizes_complete_failure_without_committing_it
    {input : State} (inputValid : input.ValidFor) {failure : Failure} {after : Remainder}
    {trace : List ParseDiagnostic}
    (rejection : TypeExprTraceRejects input.file.id input.window.endByte
      input.declarativeRemainder after failure.toDiagnostic trace) :
    ∃ rejected, typeExpr input = .reject failure rejected ∧ rejected.declarativeRemainder = after ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      ¬ ∃ value output events, TypeExprTraceParses input.file.id input.window.endByte
        input.declarativeRemainder value output events := by
  rcases (typeExpr_trace_reject_failure_iff_onValid inputValid).mp rejection with
    ⟨rejected, result, afterEq, events⟩
  exact ⟨rejected, result, afterEq, events, rejection.disjoint_success⟩

end Solcore.Test.SyntaxTypeExprTraceOutcomeProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeExprTraceProperties
/-! Public recursive execution supplies its own child trace evidence. Arbitrary
prior events remain in order, and normalization retains the entire fresh suffix;
the final rejection report is separate from that suffix. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem successful_type_keeps_ordinary_structure_and_protected_events
    {input output : State} {value : TypeExpr}
    (result : typeExpr input = .ok value output) (lexical : List LexicalDiagnostic) :
    ∃ trace,
      TypeExprTraceParses input.file.id input.window.endByte input.declarativeRemainder
        value output.declarativeRemainder trace ∧
      TypeExprParses input.declarativeRemainder value output.declarativeRemainder ∧
      output.tokens = input.tokens ∧ output.window.endIndex = input.window.endIndex ∧
      output.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical output.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases typeExpr_trace_success_sound result with ⟨trace, parsed, events⟩
  refine ⟨trace, parsed, parsed.ordinary, parsed.output_window.1,
    parsed.output_window.2, events, ?_⟩
  rw [events, filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics input.file lexical input.diagnostics ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters input.file lexical
      (parsed.cascadeFilters input.file.content (lexical.map (·.span))))

theorem rejected_type_keeps_report_separate_from_protected_events
    {input rejected : State} {failure : Failure}
    (result : typeExpr input = .reject failure rejected) (lexical : List LexicalDiagnostic) :
    ∃ trace,
      TypeExprTraceRejects input.file.id input.window.endByte input.declarativeRemainder
        rejected.declarativeRemainder failure.toDiagnostic trace ∧
      rejected.diagnostics = input.diagnostics ++ trace ∧
      filterParseDiagnostics input.file lexical rejected.diagnostics =
        filterParseDiagnostics input.file lexical input.diagnostics ++ trace := by
  rcases typeExpr_reject_trace_sound result with ⟨trace, rejection, events⟩
  refine ⟨trace, rejection, events, ?_⟩
  rw [events, filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics input.file lexical input.diagnostics ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters input.file lexical
      (rejection.cascadeFilters input.file.content (lexical.map (·.span))))

end Solcore.Test.SyntaxTypeExprTraceProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeExprTraceStateProperties
/-! Independent nested traces reconstruct whole replies with arbitrary prior
events. Separate counterexamples show why cursor-only equality cannot replace
the full-state iff when a proposed remainder has a different token carrier or
end index. No complete parser evaluation is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceStateProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

private def source : SourceId := { origin := .main, path := "whole-type-state.sol" }
private def span (startByte endByte : Nat) : SourceSpan := { source, startByte, endByte }
private def atToken : Token := { span := span 0 1, value := .symbol .at }
private def name : Identifier := { span := span 1 4, value := "a-b" }
private def nameToken : Token := { span := name.span, value := .identifier name.value }
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def successTokens : List Token := [atToken, nameToken, { span := span 4 5, value := .symbol .semicolon }]
private def rejectTokens : List Token := [atToken, nameToken,
  { span := span 4 5, value := .symbol .dot }, { span := span 5 6, value := .symbol .plus }]
private def remainder (tokens : List Token) (cursor : Nat) : Remainder := {
  tokens := tokens.toArray, endIndex := tokens.length, cursor
}
private def input (text : String) (tokens : List Token) (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := text }, tokens := tokens.toArray, cursor := 0
  window := { endIndex := tokens.length, endByte := text.utf8ByteSize }, diagnosticsRev := prior.reverse
}
private def leaf : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def value : TypeExpr := { span := SourceSpan.cover (span 0 1) leaf.span, value := .proxy (span 0 1) leaf }
private def failure : Failure := {
  span := span 5 6, found := some (.symbol .plus)
  expected := { head := .identifier, tail := [] }, context := .typeExpr
}
private def successfulState (prior : List ParseDiagnostic) : State := {
  input "@a-b;" successTokens prior with cursor := 2, diagnosticsRev := [event] ++ prior.reverse
}
private def rejectedState (prior : List ParseDiagnostic) : State := {
  input "@a-b.+" rejectTokens prior with cursor := 3, diagnosticsRev := [event] ++ prior.reverse
}

private theorem head_trace (tokens : List Token)
    (present : TokenAt tokens.toArray tokens.length 1 nameToken) :
    IdentifierTraceParses (remainder tokens 1) name (remainder tokens 2) [event] :=
  .parsed ⟨present, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))

private theorem success_trace :
    TypeExprTraceParses source 5 (remainder successTokens 0) value (remainder successTokens 2) [event] := by
  have head := head_trace successTokens ⟨by change 1 < 3; decide, rfl⟩
  have noDot : TokenKindAbsentAt successTokens.toArray successTokens.length 2 (.symbol .dot) := by
    simp [TokenKindAbsentAt, TokenAt, successTokens]
  have noArguments : TokenKindAbsentAt successTokens.toArray successTokens.length 2 (.symbol .less) := by
    simp [TokenKindAbsentAt, TokenAt, successTokens]
  have qualified : QualifiedNameTraceParses source 5 (remainder successTokens 1)
      (tracedQualifiedName name []) (remainder successTokens 2) [event] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head (DottedIdentifierTailTraceParses.done noDot)
  have named : NamedTypeTraceParses TypeExprTraceParses source 5 (remainder successTokens 1)
      leaf (remainder successTokens 2) [event] := by
    simpa only [List.append_nil, leaf] using NamedTypeTraceParses.parsed qualified
      (NamedTypeArgumentsTraceParses.absent noArguments)
      (NamedTypeFinishingTrace.ordinary (by
        unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix name
        decide))
  have child := TypeExprTraceParses.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch { input "@a-b;" successTokens [] with cursor := 1 } = .named from rfl)) named)
  have proxy : ProxyTypeTraceParses TypeExprTraceParses source 5 (remainder successTokens 0)
      value (remainder successTokens 2) [event] := by
    unfold value
    exact .parsed (span 0 1) ⟨⟨by change 0 < 3; decide, rfl⟩, rfl⟩ child
  exact TypeExprTraceParses.roll (.selected .proxy
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (input "@a-b;" successTokens []) = .proxy from rfl))
    proxy)

private theorem rejection_trace :
    TypeExprTraceRejects source 6 (remainder rejectTokens 0) (remainder rejectTokens 3)
      failure.toDiagnostic [event] := by
  have head := head_trace rejectTokens ⟨by change 1 < 4; decide, rfl⟩
  have tail : DottedIdentifierTailTraceRejects .typeExpr source 6 (remainder rejectTokens 2)
      (remainder rejectTokens 3) failure.toDiagnostic [] :=
    .componentRejected (span 4 5) ⟨⟨by change 2 < 4; decide, rfl⟩, rfl⟩
      (by simp [IdentifierAbsentAt, TokenAt, remainder, rejectTokens])
      (.reported (.token (current := { span := span 5 6, value := .symbol .plus })
        ⟨by change 3 < 4; decide, rfl⟩))
  have named : NamedTypeTraceRejects TypeExprTraceParses TypeExprTraceRejects source 6
      (remainder rejectTokens 1) (remainder rejectTokens 3) failure.toDiagnostic [event] := by
    exact .nameRejected (by simpa only [List.append_nil] using QualifiedNameTraceRejects.tailRejected head tail)
  have child := TypeExprTraceRejects.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch { input "@a-b.+" rejectTokens [] with cursor := 1 } = .named from rfl)) named)
  exact TypeExprTraceRejects.roll (.selected .proxy
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (input "@a-b.+" rejectTokens []) = .proxy from rfl))
    (.innerRejected (span 0 1) ⟨⟨by change 0 < 4; decide, rfl⟩, rfl⟩ child))

theorem nested_success_whole_state (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 5 (remainder successTokens 0) value (remainder successTokens 2) [event] ∧
    typeExpr (input "@a-b;" successTokens prior) = .ok value (successfulState prior) ∧
    (successfulState prior).diagnostics = prior ++ [event] ∧
    (successfulState prior).peek? = some { span := span 4 5, value := .symbol .semicolon } := by
  refine ⟨success_trace, ?_, ?_, rfl⟩
  · exact (typeExpr_trace_success_state_iff (input := input "@a-b;" successTokens prior)).mp success_trace
  · simp only [successfulState, State.diagnostics, List.reverse_append, List.reverse_reverse, List.reverse_singleton]

theorem nested_rejection_whole_state (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 6 (remainder rejectTokens 0) (remainder rejectTokens 3) failure.toDiagnostic [event] ∧
    typeExpr (input "@a-b.+" rejectTokens prior) = .reject failure (rejectedState prior) ∧
    (rejectedState prior).diagnostics = prior ++ [event] ∧
    (rejectedState prior).peek? = some { span := span 5 6, value := .symbol .plus } := by
  refine ⟨rejection_trace, ?_, ?_, rfl⟩
  · exact (typeExpr_trace_reject_failure_state_iff (input := input "@a-b.+" rejectTokens prior)).mp rejection_trace
  · simp only [rejectedState, State.diagnostics, List.reverse_append, List.reverse_reverse, List.reverse_singleton]

theorem nested_report_whole_state (prior : List ParseDiagnostic) :
    ∃ actual, typeExpr (input "@a-b.+" rejectTokens prior) = .reject actual (rejectedState prior) ∧
      actual.toDiagnostic = failure.toDiagnostic ∧ actual = failure := by
  rcases (typeExpr_trace_reject_state_iff (input := input "@a-b.+" rejectTokens prior)).mp rejection_trace with
    ⟨actual, result, same⟩
  exact ⟨actual, result, same, Failure.toDiagnostic_injective same⟩

private def wrongTokens : Remainder := { remainder successTokens 2 with tokens := #[] }
private def wrongEndIndex : Remainder := { remainder successTokens 2 with endIndex := 0 }

/-- Cursor-only equality stays true even though the proposed carrier cannot be an outcome. -/
theorem cursor_only_forgets_tokens (prior : List ParseDiagnostic) :
    typeExpr (input "@a-b;" successTokens prior) = .ok value
      { input "@a-b;" successTokens prior with
        cursor := wrongTokens.cursor
        diagnosticsRev := [event] ++ prior.reverse } ∧
    ¬ TypeExprTraceParses source 5 (remainder successTokens 0) value wrongTokens [event] ∧
    (input "@a-b;" successTokens prior).traceResult wrongTokens [event] ≠ successfulState prior := by
  refine ⟨(nested_success_whole_state prior).2.1, ?_, ?_⟩
  · intro wrong
    have tokenEq := congrArg Remainder.tokens (wrong.result_unique success_trace).2.1
    have sizes := congrArg Array.size tokenEq
    change 0 = 3 at sizes
    contradiction
  · intro same
    have sizes := congrArg (fun state : State => state.tokens.size) same
    change 0 = 3 at sizes
    contradiction

/-- The same issue occurs independently for a mismatched end index. -/
theorem cursor_only_forgets_endIndex (prior : List ParseDiagnostic) :
    typeExpr (input "@a-b;" successTokens prior) = .ok value
      { input "@a-b;" successTokens prior with
        cursor := wrongEndIndex.cursor
        diagnosticsRev := [event] ++ prior.reverse } ∧
    ¬ TypeExprTraceParses source 5 (remainder successTokens 0) value wrongEndIndex [event] ∧
    (input "@a-b;" successTokens prior).traceResult wrongEndIndex [event] ≠ successfulState prior := by
  refine ⟨(nested_success_whole_state prior).2.1, ?_, ?_⟩
  · intro wrong
    have indexes := congrArg Remainder.endIndex (wrong.result_unique success_trace).2.1
    change 0 = 3 at indexes
    contradiction
  · intro same
    have indexes := congrArg (fun state : State => state.window.endIndex) same
    change 0 = 3 at indexes
    contradiction

end Solcore.Test.SyntaxTypeExprTraceStateProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeExprTraceUnrestrictedExamples
/-! Reverse recursive correspondence on intentionally noncanonical states.
The carrier is shorter than its active window, token provenance is malformed,
and the source is empty. Separate missing-carrier and past-window failures
retain the complete state and leave their EOF report uncommitted. No complete
parser evaluation or input-validity assumption is used. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeExprTraceUnrestrictedExamples

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

private def source : SourceId := { origin := .main, path := "unrestricted-type.sol" }
private def alien : SourceId := { origin := .main, path := "unrelated-token.sol" }
private def file : SourceFile := { id := source, content := "" }
private def name : Identifier := {
  span := { source := alien, startByte := 50, endByte := 2 }, value := "a-b"
}
private def token : Token := { span := name.span, value := .identifier name.value }
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def value : TypeExpr := namedTypeTraceValue (tracedQualifiedName name []) none
private def state (prior : List ParseDiagnostic) (cursor : Nat) : State := {
  file, tokens := #[token], cursor, window := { endIndex := 3, endByte := 99 }
  diagnosticsRev := prior.reverse
}
private def advanced (prior : List ParseDiagnostic) : State := {
  state prior 1 with diagnosticsRev := [event] ++ prior.reverse
}
private def failure : Failure := {
  span := { source, startByte := 99, endByte := 99 }, found := none
  expected := { head := .typeExpr, tail := [] }, context := .typeExpr
}

theorem noncanonical_state (prior : List ParseDiagnostic) (cursor : Nat) :
    name.span.source ≠ (state prior cursor).file.id ∧ name.span.endByte < name.span.startByte ∧
      (state prior cursor).tokens.size < (state prior cursor).window.endIndex ∧
      (state prior cursor).file.content.utf8ByteSize < (state prior cursor).window.endByte ∧
      ¬ (state prior cursor).ValidFor := by
  refine ⟨by change alien ≠ source; decide, by decide,
    by change 1 < 3; decide, by change 0 < 99; decide, ?_⟩
  intro valid
  have bound := valid.endIndex_le_size
  change 3 ≤ 1 at bound
  omega

theorem noncanonical_ordinary_and_noInvariant (prior : List ParseDiagnostic) (cursor : Nat) :
    ((∃ result next, typeExpr (state prior cursor) = .ok result next) ∨
      (∃ error next, typeExpr (state prior cursor) = .reject error next)) ∧
      ∀ error, typeExpr (state prior cursor) ≠ .invariant error :=
  ⟨typeExpr_ordinary (state prior cursor), typeExpr_ne_invariant_unrestricted (state prior cursor)⟩

theorem noncanonical_execution_with_trace (prior : List ParseDiagnostic) (cursor : Nat) :
    (∃ result output trace, typeExpr (state prior cursor) = .ok result output ∧
      TypeExprTraceParses source 99 (state prior cursor).declarativeRemainder
        result output.declarativeRemainder trace ∧ output.diagnostics = prior ++ trace) ∨
    (∃ error rejected trace, typeExpr (state prior cursor) = .reject error rejected ∧
      TypeExprTraceRejects source 99 (state prior cursor).declarativeRemainder
        rejected.declarativeRemainder error.toDiagnostic trace ∧ rejected.diagnostics = prior ++ trace) := by
  rcases typeExpr_exists_trace_outcome (state prior cursor) with
    ⟨result, output, trace, executed, parsed, events⟩ | ⟨error, rejected, trace, executed, rejection, events⟩
  · refine .inl ⟨result, output, trace, executed, parsed, ?_⟩
    simpa only [state, State.diagnostics, List.reverse_reverse] using events
  · refine .inr ⟨error, rejected, trace, executed, rejection, ?_⟩
    simpa only [state, State.diagnostics, List.reverse_reverse] using events

private theorem malformed_leaf_trace (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 99 (state prior 0).declarativeRemainder value
      (state prior 1).declarativeRemainder [event] := by
  have tokenAt : TokenAt (state prior 0).tokens (state prior 0).window.endIndex (state prior 0).cursor token :=
    ⟨by change 0 < 3; decide, rfl⟩
  have noDot : TokenKindAbsentAt (state prior 1).tokens (state prior 1).window.endIndex
      (state prior 1).cursor (.symbol .dot) := by simp [TokenKindAbsentAt, TokenAt, state]
  have noArguments : TokenKindAbsentAt (state prior 1).tokens (state prior 1).window.endIndex
      (state prior 1).cursor (.symbol .less) := by simp [TokenKindAbsentAt, TokenAt, state]
  have head : IdentifierTraceParses (state prior 0).declarativeRemainder name
      (state prior 1).declarativeRemainder [event] :=
    .parsed ⟨tokenAt, rfl, rfl, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
  have qualified : QualifiedNameTraceParses source 99 (state prior 0).declarativeRemainder
      (tracedQualifiedName name []) (state prior 1).declarativeRemainder [event] := by
    simpa only [List.append_nil] using QualifiedNameTraceParses.parsed head
      (DottedIdentifierTailTraceParses.done noDot)
  have raw : NamedTypeTraceParses TypeExprTraceParses source 99 (state prior 0).declarativeRemainder
      value (state prior 1).declarativeRemainder [event] := by
    simpa only [List.append_nil, value] using NamedTypeTraceParses.parsed qualified
      (NamedTypeArgumentsTraceParses.absent noArguments)
      (NamedTypeFinishingTrace.ordinary (by
        unfold UnqualifiedMappingSpelling tracedQualifiedName qualifiedNameFromSuffix name
        decide))
  exact TypeExprTraceParses.roll (.selected .named
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 0) = .named from rfl)) raw)

theorem malformed_leaf_reconstructed (prior : List ParseDiagnostic) :
    TypeExprTraceParses source 99 (state prior 0).declarativeRemainder value
      (state prior 1).declarativeRemainder [event] ∧
      ∃ output, typeExpr (state prior 0) = .ok value output ∧ output = advanced prior ∧
        output.declarativeRemainder = (state prior 1).declarativeRemainder ∧
        output.diagnostics = prior ++ [event] ∧ output.file = file ∧
        output.window = { endIndex := 3, endByte := 99 } := by
  have parsed := malformed_leaf_trace prior
  rcases (typeExpr_trace_success_iff (input := state prior 0)).mp parsed with ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 0) = .ok value (advanced prior) :=
    checked_name_type (input := state prior 0) (name := name) (trace := [event])
      ⟨by change 0 < 3; decide, rfl⟩
      (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
      (by simp [TokenKindAbsentAt, TokenAt, state])
      (by simp [TokenKindAbsentAt, TokenAt, state]) (by decide) (by decide)
  rw [componentResult] at result
  cases result
  refine ⟨parsed, _, componentResult, rfl, afterEq, ?_, rfl, rfl⟩
  simpa only [state, State.diagnostics, List.reverse_reverse] using events

private theorem missing_carrier_trace (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 99 (state prior 1).declarativeRemainder
      (state prior 1).declarativeRemainder failure.toDiagnostic [] :=
  TypeExprTraceRejects.roll (.selected .final
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 1) = .final from rfl))
    (.rejected (.reported (.missingToken (by change 1 < 3; decide) rfl))))

theorem missing_carrier_reconstructed (prior : List ParseDiagnostic) :
    (state prior 1).cursor < (state prior 1).window.endIndex ∧ (state prior 1).tokens[1]? = none ∧
      TypeExprTraceRejects source 99 (state prior 1).declarativeRemainder
        (state prior 1).declarativeRemainder failure.toDiagnostic [] ∧
      ∃ output, typeExpr (state prior 1) = .reject failure output ∧ output = state prior 1 ∧
        output.declarativeRemainder = (state prior 1).declarativeRemainder ∧ output.diagnostics = prior := by
  have rejected := missing_carrier_trace prior
  rcases (typeExpr_trace_reject_failure_iff (input := state prior 1)).mp rejected with
    ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 1) = .reject failure (state prior 1) := by
    change typeExprWithFuel ((state prior 1).remainingCount + 1) (state prior 1) = _
    rw [typeExprWithFuel_eq_raw_of_selection (state prior 1).remainingCount
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state prior 1) = .final from rfl))]
    rfl
  rw [componentResult] at result
  cases result
  refine ⟨by change 1 < 3; decide, rfl, rejected, _, componentResult, rfl, afterEq, ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

private theorem past_window_trace (prior : List ParseDiagnostic) :
    TypeExprTraceRejects source 99 (state prior 7).declarativeRemainder
      (state prior 7).declarativeRemainder failure.toDiagnostic [] :=
  TypeExprTraceRejects.roll (.selected .final
    (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
      TypeDispatchTraceInternals.selectedBranch (state prior 7) = .final from rfl))
    (.rejected (.reported (.windowEnd (by change 3 ≤ 7; decide)))))

theorem past_window_reconstructed (prior : List ParseDiagnostic) :
    (state prior 7).window.endIndex < (state prior 7).cursor ∧
      TypeExprTraceRejects source 99 (state prior 7).declarativeRemainder
        (state prior 7).declarativeRemainder failure.toDiagnostic [] ∧
      ∃ output, typeExpr (state prior 7) = .reject failure output ∧ output = state prior 7 ∧
        output.declarativeRemainder = (state prior 7).declarativeRemainder ∧ output.diagnostics = prior := by
  have rejected := past_window_trace prior
  rcases (typeExpr_trace_reject_failure_iff (input := state prior 7)).mp rejected with
    ⟨output, result, afterEq, events⟩
  have componentResult : typeExpr (state prior 7) = .reject failure (state prior 7) := by
    change typeExprWithFuel ((state prior 7).remainingCount + 1) (state prior 7) = _
    rw [typeExprWithFuel_eq_raw_of_selection (state prior 7).remainingCount
      (TypeDispatchTraceInternals.selectedBranch_eq_iff.mp (show
        TypeDispatchTraceInternals.selectedBranch (state prior 7) = .final from rfl))]
    rfl
  rw [componentResult] at result
  cases result
  refine ⟨by change 3 < 7; decide, rejected, _, componentResult, rfl, afterEq, ?_⟩
  simp only [state, State.diagnostics, List.reverse_reverse]

end Solcore.Test.SyntaxTypeExprTraceUnrestrictedExamples
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeSuccessContextProperties
/-! Full source/window framing composes with the existing token-carrier law on
arbitrary inputs. A deliberately noncanonical carrier checks that no validity
or lexical provenance premise has slipped into the new contract. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeSuccessContextProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar
open Solcore.Test.SyntaxCheckedTypeLeafTraceSupport

theorem fuel_success_preserves_full_frame (fuel : Nat)
    {input output : State} {value : TypeExpr}
    (result : typeExprWithFuel fuel input = .ok value output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧ output.window = input.window := by
  have frame := typeExprWithFuel_success_context fuel result
  exact ⟨frame.1, typeExprWithFuel_preservesTokensOnSuccess fuel input value output result, frame.2⟩

theorem production_success_preserves_full_frame
    {input output : State} {value : TypeExpr} (result : typeExpr input = .ok value output) :
    output.file = input.file ∧ output.tokens = input.tokens ∧ output.window = input.window := by
  have frame := typeExpr_success_context result
  exact ⟨frame.1, typeExpr_preservesTokensOnSuccess input value output result, frame.2⟩

private def source : SourceId := { origin := .main, path := "noncanonical-type-context.sol" }
private def name : Identifier := {
  span := { source, startByte := 10, endByte := 13 }, value := "a-b"
}
private def event : ParseDiagnostic := { span := name.span, kind := .invalidIdentifierHyphen name.value }
private def input (prior : List ParseDiagnostic) : State := {
  file := { id := source, content := "" }
  tokens := #[{ span := name.span, value := .identifier name.value }]
  cursor := 0
  window := { endIndex := 9, endByte := 0 }
  diagnosticsRev := prior.reverse
}
private def output (prior : List ParseDiagnostic) : State := {
  input prior with cursor := 1, diagnosticsRev := event :: prior.reverse
}

theorem noncanonical_window_keeps_source_and_window (prior : List ParseDiagnostic) :
    (input prior).tokens.size < (input prior).window.endIndex ∧
    typeExpr (input prior) = .ok (namedTypeTraceValue (tracedQualifiedName name []) none) (output prior) ∧
    (output prior).file = (input prior).file ∧ (output prior).window = (input prior).window ∧
    (output prior).diagnostics = prior ++ [event] := by
  have result := checked_name_type (input := input prior) (name := name) (trace := [event])
    ⟨by change 0 < 9; decide, rfl⟩ (.hyphen (by unfold IdentifierHyphenSpelling name; decide))
    (by simp [TokenKindAbsentAt, TokenAt, input])
    (by simp [TokenKindAbsentAt, TokenAt, input])
    (by decide) (by decide)
  have frame := typeExpr_success_context result
  refine ⟨by change 1 < 9; decide, result, frame.1, frame.2, ?_⟩
  simp only [output, State.diagnostics, List.reverse_cons, input, List.reverse_reverse]

end Solcore.Test.SyntaxTypeSuccessContextProperties
end

section
-- leanmerge: from Solcore.Test.SyntaxTypeTraceMonotonicityProperties
/-! Forgetting child proof annotations does not forget any diagnostic event.
The enriched relation simultaneously supplies an exact underlying type trace
and duplicate-preserving normalization after arbitrary earlier reports. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxTypeTraceMonotonicityProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

variable
  {elementTrace : SourceId → Nat → Remainder → TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {elementRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

theorem success_forgets_annotations_but_keeps_events
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input output : Remainder} {value : TypeExpr} {trace : List ParseDiagnostic}
    (parsed : TypeDispatchTraceParses
      (fun source endByte input value output trace =>
        elementTrace source endByte input value output trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      source endByte input value output trace) :
    TypeDispatchTraceParses elementTrace source endByte input value output trace ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  refine ⟨parsed.mono (fun child => child.1), ?_⟩
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical (parsed.cascadeFilters (fun child => child.2)))

theorem rejection_forgets_annotations_but_keeps_report_and_events
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {input rejected : Remainder} {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TypeDispatchTraceRejects
      (fun source endByte input value output trace =>
        elementTrace source endByte input value output trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      (fun source endByte input rejected report trace =>
        elementRejects source endByte input rejected report trace ∧
          ParseDiagnosticCascadeFilters file.content (lexical.map (·.span)) trace trace)
      source endByte input rejected report trace) :
    TypeDispatchTraceRejects elementTrace elementRejects source endByte input rejected report trace ∧
      filterParseDiagnostics file lexical (prior ++ trace) = filterParseDiagnostics file lexical prior ++ trace := by
  refine ⟨rejection.mono (fun child => child.1) (fun child => child.1), ?_⟩
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters (fun child => child.2) (fun child => child.2)))

end Solcore.Test.SyntaxTypeTraceMonotonicityProperties
end
