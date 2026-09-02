import Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionSignatureOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for
complete named-function declarations.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary function declaration, including recovery-aware signature
parameters and balanced isolated-block recovery. -/
inductive FunctionDeclOrdinaryParses :
    Remainder → Syntax.FunctionDecl → Remainder → Prop where
  | parsed {input afterSignature output : Remainder}
      {signature : Syntax.FunctionSignature} {body : Syntax.Block}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .allow
        afterSignature body output) :
      FunctionDeclOrdinaryParses input {
        span := SourceSpan.cover signature.span body.span
        value := { signature, body }
      } output

/-- Exact first rejecting stage of an ordinary function-declaration attempt.
Balanced child-block rejection is represented by ordinary recovered success,
so only uncaptured body rejection escapes the declaration parser. -/
inductive FunctionDeclRejects : Remainder → Remainder → Prop where
  | signatureRejected {input rejected : Remainder}
      (signatureRejected : FunctionSignatureRejects input rejected) :
      FunctionDeclRejects input rejected
  | bodyRejected {input afterSignature rejected : Remainder}
      {signature : Syntax.FunctionSignature}
      (signatureParsed : FunctionSignatureOrdinaryParses input signature
        afterSignature)
      (bodyRejected : IsolatedCoreBlockPublicRejects .allow afterSignature
        rejected) :
      FunctionDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
