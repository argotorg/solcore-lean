import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceExactnessProperties
import Solcore.Syntax.DeclarativeOptionalLambdaReturnTypeTraceProtectionProperties
import Solcore.Syntax.Parser.OptionalLambdaReturnTypeRejectionTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

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
