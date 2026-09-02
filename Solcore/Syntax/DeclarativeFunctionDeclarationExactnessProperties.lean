import Solcore.Syntax.DeclarativeCoreBlockIsolationExactnessProperties
import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionSignatureExactnessProperties

/-!
Exactness transport through complete named-function declarations.

The function signature is unconditionally exact. The only remaining premise
is exactness of the isolated `.allow` Core body.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact isolated body makes a successful function declaration fix its
complete AST. -/
theorem FunctionDeclOrdinaryParses.value_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSignature leftBody =>
      cases rightParsed with
      | parsed rightSignature rightBody =>
          rcases functionSignatureExactOutcomeSpec.successResultUnique
              leftSignature rightSignature with
            ⟨signatureEq, afterSignatureEq⟩
          subst signatureEq
          subst afterSignatureEq
          rcases bodyOutcomes.successResultUnique leftBody rightBody with
            ⟨bodyEq, afterBodyEq⟩
          subst bodyEq
          rfl

/-- With an exact isolated body, successful function declarations fix their
AST and final remainder. -/
theorem FunctionDeclOrdinaryParses.result_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique_of_exact_body bodyOutcomes rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- With an exact isolated body, function-declaration rejection fixes its
first failing endpoint. -/
theorem FunctionDeclRejects.output_unique_of_exact_body
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow))
    {input left right : Remainder}
    (leftRejected : FunctionDeclRejects input left)
    (rightRejected : FunctionDeclRejects input right) : left = right := by
  cases leftRejected with
  | signatureRejected leftSignature =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact functionSignatureExactOutcomeSpec.rejectOutputUnique
            leftSignature rightSignature
      | bodyRejected rightSignature rightBody =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              leftSignature ⟨_, _, rightSignature⟩)
  | bodyRejected leftSignature leftBody =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              rightSignature ⟨_, _, leftSignature⟩)
      | bodyRejected rightSignature rightBody =>
          have afterSignatureEq :=
            functionSignatureExactOutcomeSpec.successOutputUnique
              leftSignature rightSignature
          subst afterSignatureEq
          exact bodyOutcomes.rejectOutputUnique leftBody rightBody

/-- An exact isolated `.allow` body lifts to exact broad function-declaration
outcomes. -/
theorem functionDeclExactOutcomeSpecOfBody
    (bodyOutcomes : ExactDeterministicOutcomeSpec
      (IsolatedCoreBlockPublicOrdinaryParses .allow)
      (IsolatedCoreBlockPublicRejects .allow)) :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects where
  toDeterministicOutcomeSpec := functionDeclDeterministicOutcomeSpec
  successValueUnique :=
    FunctionDeclOrdinaryParses.value_unique_of_exact_body bodyOutcomes
  rejectOutputUnique :=
    FunctionDeclRejects.output_unique_of_exact_body bodyOutcomes

/-- Fixed-fuel Core statement exactness supplies the isolated `.allow` body
contract and therefore exact broad function-declaration outcomes. -/
theorem functionDeclExactOutcomeSpecOfStatementFuel
    (statementOutcomes : ∀ fuel,
      ExactDeterministicOutcomeSpec
        (CoreStatementOrdinaryParsesWithFuel fuel)
        (CoreStatementRejectsWithFuel fuel)) :
    ExactDeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects :=
  functionDeclExactOutcomeSpecOfBody
    (isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel statementOutcomes
      .allow)

end Solcore.Syntax.DeclarativeGrammar
