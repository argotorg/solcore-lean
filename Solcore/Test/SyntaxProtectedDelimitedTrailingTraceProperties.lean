import Solcore.Syntax.DeclarativeDelimitedTrailingTraceProtectionProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingRejectionTraceProtectionProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Complete ordered checked-name suffixes, including repeated events, survive
actual normalization on both trailing-enabled outcomes. The final uncommitted
rejection report is separate and is not claimed to be protected. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedDelimitedTrailingTraceProperties

open Solcore.Syntax Solcore.Syntax.Parser Solcore.Syntax.DeclarativeGrammar

theorem successful_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {source : SourceId} {endByte : Nat}
    {input output : Remainder} {values : DelimitedList Expr} {trace : List ParseDiagnostic}
    (parsed : TrailingDelimitedListTraceParses opening closing allowEmpty IdentifierExpressionTraceParses
      source endByte input values output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (parsed.cascadeFilters (fun value => value.cascadeFilters _ _)))

theorem rejected_name_list_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {opening closing : Symbol} {allowEmpty : Bool} {context : ParseContext}
    {source : SourceId} {endByte : Nat} {input rejected : Remainder}
    {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : TrailingDelimitedListTraceRejects opening closing allowEmpty context
      IdentifierExpressionTraceParses IdentifierExpressionTraceRejects
      source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  exact congrArg (fun suffix => filterParseDiagnostics file lexical prior ++ suffix)
    (filterParseDiagnostics_eq_of_cascadeFilters file lexical
      (rejection.cascadeFilters (fun value => value.cascadeFilters _ _)
        (fun rejectedName => rejectedName.cascadeFilters _ _)))

end Solcore.Test.SyntaxProtectedDelimitedTrailingTraceProperties
