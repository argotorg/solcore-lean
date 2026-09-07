import Solcore.Syntax.DeclarativeParenthesizedTraceOutcomeProperties
import Solcore.Syntax.DeclarativeParenthesizedTraceProtectionProperties
import Solcore.Syntax.DeclarativeParenthesizedRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeLiteralExpressionTraceExactnessProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Concrete child exactness and protected normalization for parenthesized
expressions. Raw rejection does not commit or protect its final report. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedParenthesizedTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem checked_name_parenthesized_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses)
      (ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      source endByte :=
  parenthesizedTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte)

theorem literal_parenthesized_exact (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec (ParenthesizedExpressionTraceParses LiteralExpressionTraceParses)
      (ParenthesizedExpressionTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  parenthesizedTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

theorem successful_parenthesized_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder} {value : Expr}
    {trace : List ParseDiagnostic}
    (parsed : ParenthesizedExpressionTraceParses IdentifierExpressionTraceParses
      source endByte input value output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun name => name.cascadeFilters _ _))

theorem rejected_parenthesized_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {report : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : ParenthesizedExpressionTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected report trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun name => name.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedParenthesizedTraceProperties
