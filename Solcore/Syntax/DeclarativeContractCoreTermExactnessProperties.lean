import Solcore.Syntax.DeclarativeContractDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeContractMemberCoreExactnessProperties
import Solcore.Syntax.DeclarativeEnumDeclarationExactnessProperties

/-!
Exact contract aggregates from only the remaining Core-term premises.

Unconditional enum exactness discharges the enum branch. The resulting core
member contract lifts through derive attachment and recovery-aware bodies to
complete contract declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact public expressions and isolated Core bodies supply every remaining
core-member leaf. Enum declarations need no additional premise. -/
theorem contractMemberCoreExactOutcomeSpecOfCoreTerms
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      CoreExpressionOrdinaryParses CoreExpressionPublicRejects)
    (allowBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require)) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfLeaves expressionOutcomes
    allowBodyOutcomes requireBodyOutcomes (enumDeclExactOutcomeSpec none)

/-- Fixed-fuel expression and statement exactness alone supplies exact
attribute-free contract members. -/
theorem contractMemberCoreExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfTermFuel expressionOutcomes
    statementOutcomes (enumDeclExactOutcomeSpec none)

/-- Fixed-fuel Core-term exactness lifts through derive-aware contract-member
dispatch without further declaration premises. -/
theorem contractMemberExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects :=
  contractMemberExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

/-- Fixed-fuel Core-term exactness lifts through derive attachment and the
recovery-aware body loop to complete contract bodies. -/
theorem contractBodyExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects :=
  contractBodyExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

/-- Fixed-fuel Core expression and statement exactness is sufficient for exact
complete contract declarations, including derive attachment and recovery. -/
theorem contractDeclExactOutcomeSpecOfCoreTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses
      ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfCore
    (contractMemberCoreExactOutcomeSpecOfCoreTermFuel expressionOutcomes
      statementOutcomes)

end Solcore.Syntax.DeclarativeGrammar
