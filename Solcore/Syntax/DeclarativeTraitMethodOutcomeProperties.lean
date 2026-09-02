import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeProperties
import Solcore.Syntax.DeclarativeTraitMethodOutcomeGrammar

/-! Deterministic exact ordinary outcomes for signature-only trait methods. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary trait-method success has one final remainder. -/
theorem TraitMethodOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.TraitMethod}
    {afterLeft afterRight : Remainder}
    (leftParsed : TraitMethodOrdinaryParses input left afterLeft)
    (rightParsed : TraitMethodOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSemicolonSpan leftSignature leftSemicolon =>
      cases rightParsed with
      | parsed rightSemicolonSpan rightSignature rightSemicolon =>
          have afterSignatureEq :=
            functionSignatureDeterministicOutcomeSpec.successOutputUnique
              leftSignature rightSignature
          subst afterSignatureEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact first-stage trait-method rejection excludes every ordinary success. -/
theorem TraitMethodRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : TraitMethodRejects input rejected) :
    ¬ ∃ method output, TraitMethodOrdinaryParses input method output := by
  rintro ⟨method, output, successful⟩
  cases rejection with
  | signatureRejected signatureRejected =>
      cases successful with
      | parsed semicolonSpan signatureParsed semicolonParsed =>
          exact functionSignatureDeterministicOutcomeSpec
            |>.successRejectDisjoint signatureRejected
              ⟨_, _, signatureParsed⟩
  | semicolonMissing rejectedSignature semicolonAbsent =>
      cases successful with
      | parsed semicolonSpan successfulSignature semicolonParsed =>
          have afterSignatureEq :=
            functionSignatureDeterministicOutcomeSpec.successOutputUnique
              rejectedSignature successfulSignature
          subst afterSignatureEq
          exact absent_conflicts_exact semicolonAbsent semicolonParsed

/-- Signature-only trait methods have deterministic and exclusive ordinary
outcomes. -/
theorem traitMethodDeterministicOutcomeSpec :
    DeterministicOutcomeSpec TraitMethodOrdinaryParses TraitMethodRejects where
  successOutputUnique := TraitMethodOrdinaryParses.output_unique
  successRejectDisjoint := TraitMethodRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
