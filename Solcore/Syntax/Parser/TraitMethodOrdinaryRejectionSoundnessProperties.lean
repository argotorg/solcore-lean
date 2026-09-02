import Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.FunctionSignatureOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.Trait

/-! Exact broad ordinary rejection for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- Every executable trait-method rejection occurs in its broad signature or
at its exact, non-consuming missing-semicolon stage. -/
theorem traitMethod_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : traitMethod input = .reject failure rejected) :
    DeclarativeGrammar.TraitMethodRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold traitMethod at result
  cases signatureResult : functionSignature .module input with
  | invariant error => simp [bind, signatureResult] at result
  | reject signatureFailure signatureRejected =>
      simp only [bind, signatureResult] at result
      cases result
      exact .signatureRejected
        (functionSignature_reject_ordinaryOutcome_sound .module
          signatureResult)
  | ok signature afterSignature =>
      simp only [bind, signatureResult] at result
      have signatureParsed := functionSignature_success_ordinaryOutcome_sound
        .module signatureResult
      cases semicolonResult : symbol .semicolon .topItem afterSignature with
      | invariant error => simp [semicolonResult] at result
      | ok semicolon output => simp [semicolonResult, pure] at result
      | reject semicolonFailure semicolonRejected =>
          have semicolonRejectedEq := symbol_reject_state_eq .semicolon
            .topItem semicolonResult
          subst semicolonRejected
          simp only [semicolonResult] at result
          cases result
          exact .semicolonMissing signatureParsed
            (symbol_reject_tokenKindAbsentAt .semicolon .topItem
              semicolonResult)

end Solcore.Syntax.Parser.TraitInternals
