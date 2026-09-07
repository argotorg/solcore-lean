import Solcore.Syntax.DeclarativeLiteralDiagnosticTraceProperties
import Solcore.Syntax.DeclarativeReturnStatementTraceExactnessProperties

/-! Concrete literal-expression traces discharge both independent expression
assumptions and supply exact return-only block outcomes without abstract laws. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

theorem literalExpressionTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    ExpressionTraceExactOutcomeSpec LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte where
  successResultUnique := LiteralExpressionTraceParses.result_unique
  rejectResultUnique := CoreLiteralTraceRejects.result_unique
  successRejectDisjoint := by
    intro input rejected diagnostic trace rejection
    rintro ⟨value, output, events, parsed⟩
    exact LiteralExpressionTraceRejects.disjoint_success rejection parsed

theorem literalExpressionTraceOutcomeExists (source : SourceId) (endByte : Nat) :
    ExpressionTraceOutcomeExists LiteralExpressionTraceParses LiteralExpressionTraceRejects
      source endByte :=
  literalExpressionTrace_outcome_total source endByte

theorem literalReturnStatementTraceExactOutcomeSpec (source : SourceId) (endByte : Nat) :
    StatementTraceExactOutcomeSpec (ReturnStatementTraceParses LiteralExpressionTraceParses)
      (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects)
      source endByte :=
  returnStatementTraceExactOutcomeSpec (literalExpressionTraceExactOutcomeSpec source endByte)

/-- Empty returns and one-literal returns have an independent ordinary
outcome on every carrier, including exact reports for malformed inputs. -/
theorem literalReturnStatementTrace_exists_outcome
    (source : SourceId) (endByte : Nat) (input : Remainder) :
    (∃ statement output trace,
      ReturnStatementTraceParses LiteralExpressionTraceParses source endByte
        input statement output trace) ∨
    (∃ rejected diagnostic trace,
      ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects
        source endByte input rejected diagnostic trace) :=
  returnStatementTrace_exists_outcome (literalExpressionTraceOutcomeExists source endByte) input

theorem literalReturnCoreBlockTraceExactOutcomeSpec
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy)
      (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
        (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy)
      source endByte :=
  returnCoreBlockTraceExactOutcomeSpec policy (literalExpressionTraceExactOutcomeSpec source endByte)

theorem isolatedLiteralReturnCoreBlockTraceExactOutcomeSpec
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses
        (CoreBlockTraceParses (ReturnStatementTraceParses LiteralExpressionTraceParses) policy)
        (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
          (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy))
      (IsolatedBlockTraceRejects
        (CoreBlockTraceRejects (ReturnStatementTraceParses LiteralExpressionTraceParses)
          (ReturnStatementTraceRejects LiteralExpressionTraceParses LiteralExpressionTraceRejects) policy))
      source endByte :=
  isolatedReturnCoreBlockTraceExactOutcomeSpec policy (literalExpressionTraceExactOutcomeSpec source)

end Solcore.Syntax.DeclarativeGrammar
