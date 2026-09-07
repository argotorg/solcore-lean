import Solcore.Syntax.DeclarativeDotConstructorTraceOutcomeProperties
import Solcore.Syntax.DeclarativeDotConstructorRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Concrete child exactness and full diagnostic normalization compose at the
leading-dot constructor boundary without assuming recursive expression laws. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDotConstructorTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

theorem checked_name_constructor_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses IdentifierExpressionTraceParses)
      (DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  dotConstructorTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem checked_name_optional_arguments_exact (source : SourceId) (endByte : Nat) :
    TraceExactOutcomeSpec (OptionalDotConstructorArgumentsTraceParses IdentifierExpressionTraceParses)
      (OptionalDotConstructorArgumentsTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  optionalDotConstructorArgumentsTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem literal_constructor_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (DotConstructorTraceParses LiteralExpressionTraceParses)
      (DotConstructorTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  dotConstructorTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

/-- Normalizing earlier diagnostics cannot remove or reorder the constructor
name and successful argument events preceding a rejected checked-name child.
The final unexpected-token report is separate and is not protected here. -/
theorem rejected_name_constructor_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : DotConstructorTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun name => name.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedDotConstructorTraceProperties
