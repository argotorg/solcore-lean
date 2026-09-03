import Solcore.Syntax.DeclarativeContractCoreTermExactnessProperties
import Solcore.Syntax.DeclarativeCoreTermPublicExactnessProperties
import Solcore.Syntax.DeclarativeImplDeclarationExactnessProperties

/-!
Unconditional exact Core declarations from exact recursive Core terms.

The existing conditional declarations retain their signatures. These thin
specializations discharge their body and initializer premises using the closed
Core term fuel induction, including isolated-body recovery and derive layers.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Function declarations have exact ordinary ASTs and rejection endpoints. -/
theorem functionDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects :=
  functionDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Constructor declarations have exact ordinary outcomes without body premises. -/
theorem constructorDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ConstructorDeclOrdinaryParses
      ConstructorDeclRejects :=
  constructorDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Fallback declarations have exact ordinary outcomes without body premises. -/
theorem fallbackDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec FallbackDeclOrdinaryParses
      FallbackDeclRejects :=
  fallbackDeclExactOutcomeSpecOfStatementFuel
    coreStatementExactOutcomeSpecWithFuel

/-- Implementation methods have unconditional exact ordinary outcomes. -/
theorem implMethodExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses ImplMethodRejects :=
  implMethodExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Implementation bodies have unconditional exact method lists and spans. -/
theorem implBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplBodyOrdinaryOutcomeParses ImplBodyRejects :=
  implBodyExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Complete implementation declarations have unconditional exact outcomes. -/
theorem implDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ImplDeclOrdinaryParses ImplDeclRejects :=
  implDeclExactOutcomeSpecOfStatementFuel coreStatementExactOutcomeSpecWithFuel

/-- Fields with public Core-expression initializers have unconditional exact
outcomes; the generic expression-parameterized field contract remains available. -/
theorem contractFieldPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses CoreExpressionOrdinaryParses)
      (ContractFieldRejects CoreExpressionOrdinaryParses
        CoreExpressionPublicRejects) :=
  contractFieldExactOutcomeSpec coreExpressionPublicExactOutcomeSpec

/-- Attribute-free contract-member dispatch has unconditional exact outcomes. -/
theorem contractMemberCoreExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberCoreOrdinaryParses
      ContractMemberCoreRejects :=
  contractMemberCoreExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Derive-aware contract members have unconditional exact ordinary outcomes. -/
theorem contractMemberExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractMemberOrdinaryParses
      ContractMemberRejects :=
  contractMemberExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Recovery-aware contract bodies have unconditional exact values and endpoints. -/
theorem contractBodyExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractBodyOrdinaryOutcomeParses
      ContractBodyRejects :=
  contractBodyExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

/-- Complete contract declarations have unconditional exact ordinary outcomes. -/
theorem contractDeclExactOutcomeSpec :
    ExactDeterministicOutcomeSpec ContractDeclOrdinaryParses ContractDeclRejects :=
  contractDeclExactOutcomeSpecOfCoreTermFuel
    coreExpressionExactOutcomeSpecWithFuel coreStatementExactOutcomeSpecWithFuel

end Solcore.Syntax.DeclarativeGrammar
