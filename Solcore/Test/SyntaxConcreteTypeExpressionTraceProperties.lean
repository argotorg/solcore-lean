import Solcore.Syntax.Parser.ProxyExpressionTypeTraceProperties
import Solcore.Syntax.Parser.OptionalLambdaReturnTypeConcreteTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

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
