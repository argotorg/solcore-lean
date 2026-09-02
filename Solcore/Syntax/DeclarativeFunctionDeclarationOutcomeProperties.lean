import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties

/-!
Functionality and rejection exclusivity for ordinary named-function
declaration outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary function-declaration success has one final remainder. -/
theorem FunctionDeclOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.FunctionDecl}
    {afterLeft afterRight : Remainder}
    (leftParsed : FunctionDeclOrdinaryParses input left afterLeft)
    (rightParsed : FunctionDeclOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSignature leftBody =>
      cases rightParsed with
      | parsed rightSignature rightBody =>
          have afterSignatureEq := leftSignature.output_unique rightSignature
          subst afterSignatureEq
          exact (isolatedCoreBlockPublicOutcomeSpec .allow)
            |>.successOutputUnique leftBody rightBody

/-- Exact first-stage declaration rejection excludes every ordinary success. -/
theorem FunctionDeclRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : FunctionDeclRejects input rejected) :
    ¬ ∃ declaration output,
      FunctionDeclOrdinaryParses input declaration output := by
  rintro ⟨declaration, output, successful⟩
  cases successful with
  | parsed successfulSignature successfulBody =>
      cases rejection with
      | signatureRejected signatureRejected =>
          exact functionSignatureDeterministicOutcomeSpec
            |>.successRejectDisjoint signatureRejected
              ⟨_, _, successfulSignature⟩
      | bodyRejected rejectedSignature bodyRejected =>
          have afterSignatureEq := rejectedSignature.output_unique
            successfulSignature
          subst afterSignatureEq
          exact (isolatedCoreBlockPublicOutcomeSpec .allow)
            |>.successRejectDisjoint bodyRejected ⟨_, _, successfulBody⟩

/-- Complete named-function declarations have deterministic and exclusive
ordinary outcomes. -/
theorem functionDeclDeterministicOutcomeSpec :
    DeterministicOutcomeSpec FunctionDeclOrdinaryParses
      FunctionDeclRejects where
  successOutputUnique := FunctionDeclOrdinaryParses.output_unique
  successRejectDisjoint := FunctionDeclRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
