import Solcore.Syntax.DeclarativeYulAssignmentOutcomeProperties
import Solcore.Syntax.DeclarativeYulExpressionFuelGrammar

/-!
Concrete parser-independent transactional assignment fallback for the public
recursive inline-Yul expression grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional Yul-assignment fallback induced by the complete public
expression outcome contract. -/
def yulAssignmentPublicFallbackSpec :
    YulAssignmentFallbackSpec YulExpressionParses :=
  YulAssignmentFallbackSpec.ofOutcomes YulExpressionOrdinaryParses
    YulExpressionParses YulExpressionRejects
    yulExpressionPublicDeterministicOutcomeSpec
    YulExpressionParses.toOrdinary

/-- The concrete fallback records exactly an existential public-expression
assignment rejection. -/
@[simp] theorem yulAssignmentPublicFallbackSpec_rejects_iff
    {input : Remainder} :
    yulAssignmentPublicFallbackSpec.rejects input ↔
      YulAssignmentFallbackRejects YulExpressionRejects input := by
  rfl

end Solcore.Syntax.DeclarativeGrammar
