import Solcore.Syntax.DeclarativeArrayLiteralTraceProperties
import Solcore.Syntax.DeclarativeExpressionNameTraceProtectionProperties
import Solcore.Syntax.DeclarativeReturnStatementTraceExactnessProperties
import Solcore.Syntax.DeclarativeRejectionTraceProtectionProperties
import Solcore.Syntax.Parser.ParseDiagnosticCascadeStabilityProperties

/-! Checked-name arrays discharge exactness and protected-event assumptions
through returns and raw/isolated blocks. These are restricted independent trace
instances, not outcome-existence or general recursive expression claims. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxProtectedArrayReturnTraceProperties

open Solcore.Syntax
open Solcore.Syntax.Parser
open Solcore.Syntax.DeclarativeGrammar

private abbrev arrayTrace := ArrayLiteralTraceParses IdentifierExpressionTraceParses
private abbrev arrayRejects := ArrayLiteralTraceRejects IdentifierExpressionTraceParses
  IdentifierExpressionTraceRejects
private abbrev returnTrace := ReturnStatementTraceParses arrayTrace
private abbrev returnRejects := ReturnStatementTraceRejects arrayTrace arrayRejects

theorem array_return_statement_exact (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec returnTrace returnRejects source endByte :=
  returnStatementTraceExactOutcomeSpec
    (arrayLiteralTraceExactOutcomeSpec (identifierExpressionTrace_exactOutcomeSpec source endByte))

theorem array_return_block_exact (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses returnTrace policy)
      (CoreBlockTraceRejects returnTrace returnRejects policy) source endByte :=
  coreBlockTraceExactOutcomeSpec policy (array_return_statement_exact source endByte)

theorem isolated_array_return_block_exact
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses returnTrace policy)
        (CoreBlockTraceRejects returnTrace returnRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects returnTrace returnRejects policy))
      source endByte :=
  isolatedCoreBlockTraceExactOutcomeSpec policy (array_return_statement_exact source)

private theorem return_protected
    {source : SourceId} {endByte : Nat} {input output : Remainder}
    {statement : Statement} {trace : List ParseDiagnostic}
    (parsed : returnTrace source endByte input statement output trace)
    (text : String) (lexical : List SourceSpan) : ParseDiagnosticCascadeFilters text lexical trace trace :=
  parsed.cascadeFilters (fun values => values.cascadeFilters (fun name => name.cascadeFilters text lexical))

theorem successful_array_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input output : Remainder} {body : Block} {trace : List ParseDiagnostic}
    (parsed : CoreBlockTraceParses returnTrace policy source endByte input body output trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  exact filterParseDiagnostics_eq_of_cascadeFilters file lexical
    (parsed.cascadeFilters (fun returned => return_protected returned _ _))

/-- Earlier array-name events survive raw rejection, but its separate final
report is not asserted to survive normalization if a caller later commits it. -/
theorem rejected_array_return_block_keeps_complete_suffix
    (file : SourceFile) (lexical : List LexicalDiagnostic) (prior : List ParseDiagnostic)
    {source : SourceId} {endByte : Nat} {policy : CoreBlockTailPolicy}
    {input rejected : Remainder} {diagnostic : ParseDiagnostic} {trace : List ParseDiagnostic}
    (rejection : CoreBlockTraceRejects returnTrace returnRejects policy source endByte
      input rejected diagnostic trace) :
    filterParseDiagnostics file lexical (prior ++ trace) =
      filterParseDiagnostics file lexical prior ++ trace := by
  rw [filterParseDiagnostics_append]
  congr 1
  apply filterParseDiagnostics_eq_of_cascadeFilters
  exact rejection.cascadeFilters (fun returned => return_protected returned _ _)
    (fun rejectedReturn => rejectedReturn.cascadeFilters
      (fun values => values.cascadeFilters (fun name => name.cascadeFilters _ _))
      (fun rejectedArray => ArrayLiteralTraceRejects.cascadeFilters
        (fun name => name.cascadeFilters _ _) (fun rejectedName => rejectedName.cascadeFilters _ _) rejectedArray))

end Solcore.Test.SyntaxProtectedArrayReturnTraceProperties
