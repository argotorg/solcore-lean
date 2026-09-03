import Solcore.Syntax.DeclarativeYulBodyGrammar
import Solcore.Syntax.DeclarativeYulStatementExactnessProperties

/-! Fully exact public inline-Yul body ASTs, source spans, and endpoints. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Public Yul bodies have exact successful block values and rejecting endpoints. -/
theorem yulBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulBodyOutcomeParses YulBodyRejects :=
  yulBlockExactOutcomeSpec yulStatementExactOutcomeSpec

/-- Public Yul bodies fix their span, source-order statements, and complete remainder. -/
theorem YulBodyOrdinaryParses.result_unique
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt} {afterLeft afterRight : Remainder}
    (leftParsed : YulBodyOrdinaryParses input leftSpan leftBody afterLeft)
    (rightParsed : YulBodyOrdinaryParses input rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight :=
  YulBlockParses.result_unique yulStatementExactOutcomeSpec leftParsed rightParsed

/-- Public Yul body rejection fixes the complete first-failure endpoint. -/
theorem YulBodyRejects.output_unique {input left right : Remainder}
    (leftRejected : YulBodyRejects input left)
    (rightRejected : YulBodyRejects input right) : left = right :=
  yulBodyExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
