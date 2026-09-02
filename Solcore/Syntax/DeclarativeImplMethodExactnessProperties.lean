import Solcore.Syntax.DeclarativeFunctionDeclarationExactnessProperties
import Solcore.Syntax.DeclarativeImplMethodOutcomeProperties

/-!
Exactness transport through implementation-method wrappers.

The only remaining premise is exactness of the isolated `.allow` body used by
the nested function declaration.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact isolated function body makes an implementation method fix its
wrapped declaration AST. -/
theorem ImplMethodOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftDeclaration =>
      cases rightParsed with
      | parsed rightDeclaration =>
          have declarationEq :=
            (functionDeclExactOutcomeSpecOfBody bodyOutcomes)
              |>.successValueUnique leftDeclaration rightDeclaration
          subst declarationEq
          rfl

/-- With an exact isolated function body, an implementation-method success
fixes its AST and final remainder. -/
theorem ImplMethodOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.ImplMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : ImplMethodOrdinaryParses input left afterLeft)
    (rightParsed : ImplMethodOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- With an exact isolated function body, implementation-method rejection
fixes its endpoint. -/
theorem ImplMethodRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : ImplMethodRejects input left)
    (rightRejected : ImplMethodRejects input right) : left = right := by
  cases leftRejected with
  | declarationRejected leftDeclaration =>
      cases rightRejected with
      | declarationRejected rightDeclaration =>
          exact (functionDeclExactOutcomeSpecOfBody bodyOutcomes)
            |>.rejectOutputUnique leftDeclaration rightDeclaration

/-- An exact isolated `.allow` body lifts to exact implementation-method
outcomes. -/
theorem implMethodExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses
      ImplMethodRejects where
  toDeterministicOutcomeSpec := implMethodDeterministicOutcomeSpec
  successValueUnique :=
    ImplMethodOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    ImplMethodRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core-statement exactness supplies the isolated function body
contract needed for exact implementation-method outcomes. -/
theorem implMethodExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec ImplMethodOrdinaryParses
      ImplMethodRejects :=
  implMethodExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)

end Solcore.Syntax.DeclarativeGrammar
