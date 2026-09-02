import Solcore.Syntax.DeclarativeFunctionSignatureExactnessProperties
import Solcore.Syntax.DeclarativeTraitMethodOutcomeProperties

/-! Exact values and rejection endpoints for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A successful trait method fixes its complete AST. -/
theorem TraitMethodOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSemicolonSpan leftSignature leftSemicolon =>
      cases rightParsed with
      | parsed rightSemicolonSpan rightSignature rightSemicolon =>
          rcases functionSignatureExactOutcomeSpec.successResultUnique
              leftSignature rightSignature with
            ⟨signatureEq, afterSignatureEq⟩
          subst signatureEq
          subst afterSignatureEq
          rcases leftSemicolon.result_unique rightSemicolon with
            ⟨semicolonSpanEq, afterSemicolonEq⟩
          subst semicolonSpanEq
          rfl

/-- A successful trait method fixes its AST and final remainder. -/
theorem TraitMethodOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed,
    leftParsed.output_unique rightParsed⟩

/-- Trait-method rejection fixes its first failing endpoint. -/
theorem TraitMethodRejects.output_unique
    {input left right : Remainder}
    (leftRejected : TraitMethodRejects input left)
    (rightRejected : TraitMethodRejects input right) : left = right := by
  cases leftRejected with
  | signatureRejected leftSignature =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact functionSignatureExactOutcomeSpec.rejectOutputUnique
            leftSignature rightSignature
      | semicolonMissing rightSignature rightSemicolonAbsent =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              leftSignature ⟨_, _, rightSignature⟩)
  | semicolonMissing leftSignature leftSemicolonAbsent =>
      cases rightRejected with
      | signatureRejected rightSignature =>
          exact False.elim
            (functionSignatureExactOutcomeSpec.successRejectDisjoint
              rightSignature ⟨_, _, leftSignature⟩)
      | semicolonMissing rightSignature rightSemicolonAbsent =>
          exact functionSignatureExactOutcomeSpec.successOutputUnique
            leftSignature rightSignature

/-- Signature-only trait methods have fully exact ordinary outcomes. -/
theorem traitMethodExactOutcomeSpec :
    ExactDeterministicOutcomeSpec TraitMethodOrdinaryParses
      TraitMethodRejects where
  toDeterministicOutcomeSpec := traitMethodDeterministicOutcomeSpec
  successValueUnique := TraitMethodOrdinaryParses.value_unique
  rejectOutputUnique := TraitMethodRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
