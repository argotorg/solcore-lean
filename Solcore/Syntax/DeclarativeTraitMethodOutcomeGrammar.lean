import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for one
signature-only trait method.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An ordinary trait method is a broad ordinary function signature followed
by its exact terminating semicolon. -/
inductive TraitMethodOrdinaryParses :
    Remainder → Syntax.TraitMethod → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} (semicolonSpan : SourceSpan)
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon)
        afterSignature semicolonSpan output) :
      TraitMethodOrdinaryParses input {
        span := SourceSpan.cover signature.span semicolonSpan
        value := {
          leadingComments := []
          signature
          semicolon := semicolonSpan
        }
      } output

/-- Exact first rejecting stage of an ordinary trait-method attempt. -/
inductive TraitMethodRejects : Remainder → Remainder → Prop where
  | signatureRejected {input rejected : Remainder}
      (signatureRejected : FunctionSignatureRejects input rejected) :
      TraitMethodRejects input rejected
  | semicolonMissing {input afterSignature : Remainder}
      {signature : Syntax.FunctionSignature}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (semicolonAbsent : TokenKindAbsentAt afterSignature.tokens
        afterSignature.endIndex afterSignature.cursor (.symbol .semicolon)) :
      TraitMethodRejects input afterSignature

end Solcore.Syntax.DeclarativeGrammar
