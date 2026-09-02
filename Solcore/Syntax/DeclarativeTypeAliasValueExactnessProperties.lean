import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativeTypeAliasValueRecoveryExactnessProperties

/-! Unconditional exactness of recovery-aware type-alias values. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recovery-aware alias-value success constructs one exact type AST. -/
theorem TypeAliasValueOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right :=
  leftParsed.value_unique_of_typeExpr typeExprExactOutcomeSpec rightParsed

/-- Recovery-aware alias-value success fixes its AST and final remainder. -/
theorem TypeAliasValueOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : TypeAliasValueOrdinaryParses input left afterLeft)
    (rightParsed : TypeAliasValueOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  leftParsed.result_unique_of_typeExpr typeExprExactOutcomeSpec rightParsed

/-- Recovery-aware type-alias values have fully exact ordinary outcomes. -/
theorem typeAliasValueExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TypeAliasValueOrdinaryParses
      TypeAliasValueRejects :=
  typeAliasValueExactOutcomeSpecOfTypeExpr typeExprExactOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
