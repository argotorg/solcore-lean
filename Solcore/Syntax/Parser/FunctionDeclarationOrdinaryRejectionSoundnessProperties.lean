import Solcore.Syntax.DeclarativeFunctionDeclarationOutcomeGrammar
import Solcore.Syntax.Parser.CoreBlockPublicIsolationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Function
import Solcore.Syntax.Parser.FunctionSignatureOrdinaryOutcomeSoundnessProperties

/-! Exact executable rejection of complete named-function declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable declaration rejection occurs in its signature or after
ordinary signature success in the uncaptured isolated body. -/
theorem functionDecl_reject_ordinaryOutcome_sound
    (location : FunctionLocation) {input rejected : State}
    {failure : Failure}
    (result : functionDecl location input = .reject failure rejected) :
    DeclarativeGrammar.FunctionDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold functionDecl at result
  cases signatureResult : functionSignature location input with
  | invariant error => simp [bind, signatureResult] at result
  | reject signatureFailure signatureRejected =>
      simp only [bind, signatureResult] at result
      cases result
      exact .signatureRejected
        (functionSignature_reject_ordinaryOutcome_sound location
          signatureResult)
  | ok signature afterSignature =>
      simp only [bind, signatureResult] at result
      have signatureParsed :=
        functionSignature_success_ordinaryOutcome_sound location
          signatureResult
      cases bodyResult : isolateBlock (block .allow) afterSignature with
      | invariant error => simp [bodyResult] at result
      | ok body afterBody => simp [bodyResult, pure] at result
      | reject bodyFailure bodyRejected =>
          simp only [bodyResult] at result
          cases result
          exact .bodyRejected signatureParsed
            (isolatedCoreBlockPublic_reject_ordinary_sound .allow bodyResult)

end Solcore.Syntax.Parser
