import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Actual diagnostic normalization keeps complete checked-name event suffixes
through return-only blocks. Earlier diagnostics may still be filtered normally. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedStatementTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private theorem return_protected
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : ReturnStatementTraceParses IdentifierExpressionTraceParses
      source endByte input statement output trace) (text : String) (lexical : List SourceSpan) :
    ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun value => value.cascadeFilters text lexical)

/-- Lexical errors may remove prior cascade candidates, but never any fresh
name event from the complete raw return-block trace, even repeated payloads. -/
theorem successful_name_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      policy source endByte input body output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun statement => return_protected statement _ _))

/-- The same holds when a later return rejects. Its uncommitted final report
is separate; this theorem intentionally does not include or protect that report. -/
theorem rejected_name_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects (ReturnStatementTraceParses IdentifierExpressionTraceParses)
      (ReturnStatementTraceRejects IdentifierExpressionTraceParses IdentifierExpressionTraceRejects)
      policy source endByte input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact rejection.cascadeFilters (fun statement => return_protected statement _ _)
    (fun rejectedReturn => rejectedReturn.cascadeFilters
      (fun value => value.cascadeFilters _ _) (fun rejectedName => rejectedName.cascadeFilters _ _))

/-- One extra raw block-statement wrapper still preserves all events; the
inner block's ordered tail constraints are protected along with checked names. -/
theorem nested_name_return_statement_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : BlockStatementTraceParses
      (BlockStatementTraceParses (ReturnStatementTraceParses IdentifierExpressionTraceParses))
      source endByte input statement output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun inner => inner.cascadeFilters
      (fun returned => return_protected returned _ _)))

end Solcore.Test.SyntaxProtectedStatementTraceProperties
