import Solcore.Syntax.DeclarativeDelimitedNoTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Complete checked-name suffixes survive actual normalization through
no-trailing lists. A later rejection does not erase successful earlier names,
and its separate uncommitted report is deliberately outside this guarantee. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDelimitedTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

theorem successful_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {source : SourceId} {endByte : Nat}
    {input output : Remainder} {values : DelimitedList Expr} {trace : List ParseDiagnostic}
    (parsed : NoTrailingDelimitedListTraceParses opening closing allowEmpty IdentifierExpressionTraceParses
      source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun value => value.cascadeFilters _ _))

theorem rejected_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : NoTrailingDelimitedListTraceRejects opening closing allowEmpty context
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (rejection.cascadeFilters (fun value => value.cascadeFilters _ _)
      (fun rejectedName => rejectedName.cascadeFilters _ _))

end Solcore.Test.SyntaxProtectedDelimitedTraceProperties
