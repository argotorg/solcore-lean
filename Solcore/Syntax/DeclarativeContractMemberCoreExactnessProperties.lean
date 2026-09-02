import Solcore.Syntax.DeclarativeConstructorDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeContractFieldExactnessProperties
import Solcore.Syntax.DeclarativeContractMemberCoreOutcomeProperties
import Solcore.Syntax.DeclarativeFallbackDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeFunctionDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeTypeAliasDeclarationExactnessProperties

/-!
Exactness transport through attribute-free contract-member dispatch.

Type aliases are unconditionally exact. The remaining premises expose the
Core expression, isolated Core bodies, and enum outcome leaves that have not
yet been proved exact globally.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem contractMemberCore_present_conflicts_absent
    {input : Remainder} {kind : TokenKind}
    (present : ContractMemberCoreTokenPresentAt input kind)
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind) :
    False :=
  absent present

/-- Exact selected child outcomes make broad core-member success fix its AST. -/
theorem ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 10) [contractMemberCore_present_conflicts_absent,
      fieldOutcomes.successValueUnique,
      functionOutcomes.successValueUnique,
      constructorOutcomes.successValueUnique,
      fallbackOutcomes.successValueUnique,
      typeAliasDeclExactOutcomeSpec.successValueUnique,
      enumOutcomes.successValueUnique]

/-- Exact selected children make broad core-member success fix its AST and
final remainder. -/
theorem ContractMemberCoreOrdinaryParses.result_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input : Remainder} {left right : Syntax.ContractMember}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractMemberCoreOrdinaryParses input left afterLeft)
    (rightParsed : ContractMemberCoreOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_children fieldOutcomes functionOutcomes
      constructorOutcomes fallbackOutcomes enumOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Exact selected child outcomes make broad core-member rejection fix its
selected failure endpoint. -/
theorem ContractMemberCoreRejects.output_unique_of_exact_children
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects)
    {input left right : Remainder}
    (leftRejected : ContractMemberCoreRejects input left)
    (rightRejected : ContractMemberCoreRejects input right) : left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind (ematch := 10) [contractMemberCore_present_conflicts_absent,
      fieldOutcomes.rejectOutputUnique,
      functionOutcomes.rejectOutputUnique,
      constructorOutcomes.rejectOutputUnique,
      fallbackOutcomes.rejectOutputUnique,
      typeAliasDeclExactOutcomeSpec.rejectOutputUnique,
      enumOutcomes.rejectOutputUnique]

/-- Exact branch contracts lift through attribute-free contract-member
dispatch. -/
theorem contractMemberCoreExactOutcomeSpecOfChildren
    (fieldOutcomes : ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects))
    (functionOutcomes : ExactDeterministicOutcomeSpec
      FunctionDeclOrdinaryParses FunctionDeclRejects)
    (constructorOutcomes : ExactDeterministicOutcomeSpec
      ConstructorDeclOrdinaryParses ConstructorDeclRejects)
    (fallbackOutcomes : ExactDeterministicOutcomeSpec
      FallbackDeclOrdinaryParses FallbackDeclRejects)
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects where
  toDeterministicOutcomeSpec := contractMemberCoreDeterministicOutcomeSpec
  successValueUnique :=
    ContractMemberCoreOrdinaryParses.value_unique_of_exact_children
      fieldOutcomes functionOutcomes constructorOutcomes fallbackOutcomes
      enumOutcomes
  rejectOutputUnique :=
    ContractMemberCoreRejects.output_unique_of_exact_children fieldOutcomes
      functionOutcomes constructorOutcomes fallbackOutcomes enumOutcomes

/-- Exact public expressions, isolated bodies, and enums discharge every
remaining core-member leaf. The `.require` body contract is shared by
constructors and fallbacks. -/
theorem contractMemberCoreExactOutcomeSpecOfLeaves
    (expressionOutcomes : ExactDeterministicOutcomeSpec
      CoreExpressionOrdinaryParses CoreExpressionPublicRejects)
    (allowBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    (requireBodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .require)
      (IsolatedCoreBlockPublicRejects .require))
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfChildren
    (contractFieldExactOutcomeSpec expressionOutcomes)
    (functionDeclExactOutcomeSpecOfBody allowBodyOutcomes)
    (constructorDeclExactOutcomeSpecOfBody requireBodyOutcomes)
    (fallbackDeclExactOutcomeSpecOfBody requireBodyOutcomes)
    enumOutcomes

private theorem contractMemberCoreExpressionExactOutcomeSpecOfFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec CoreExpressionOrdinaryParses
      CoreExpressionPublicRejects where
  toDeterministicOutcomeSpec := coreExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (expressionOutcomes (coreExpressionPublicFuel input))
      |>.successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (expressionOutcomes (coreExpressionPublicFuel input))
      |>.rejectOutputUnique leftRejected rightRejected

/-- Fixed-fuel Core expression and statement exactness supplies all Core-term
leaves; enum exactness remains the sole non-Core premise. -/
theorem contractMemberCoreExactOutcomeSpecOfTermFuel
    (expressionOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreExpressionOrdinaryParsesWithFuel fuel)
        (CoreExpressionRejectsWithFuel fuel))
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel))
    (enumOutcomes : ExactDeterministicOutcomeSpec
      (EnumDeclOrdinaryParses none) EnumDeclRejects) :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfLeaves
    (contractMemberCoreExpressionExactOutcomeSpecOfFuel expressionOutcomes)
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .require)
    enumOutcomes

end Solcore.Syntax.DeclarativeGrammar
