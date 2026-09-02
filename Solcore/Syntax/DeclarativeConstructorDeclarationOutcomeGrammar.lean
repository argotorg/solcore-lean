import Solcore.Syntax.DeclarativeCoreBlockPublicIsolationOutcomeProperties
import Solcore.Syntax.DeclarativeFunctionParametersOutcomeGrammar

/-!
Parser-independent ordinary success and exact sequential rejection for
canonical contract constructors.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact fixed-order ordinary entry modifiers.  The optional explicit
`public` marker remains in the derivation even though the executable AST keeps
only the optional `payable` marker. -/
inductive ContractEntryModifiersOrdinaryParses :
    Remainder → Option SourceSpan → Remainder → Prop where
  | parsed {input afterPublic output : Remainder}
      {publicMarker payableMarker : Option SourceSpan}
      (publicParsed : OptionalFunctionModifierParses .publicKw input
        publicMarker afterPublic)
      (payableParsed : OptionalFunctionModifierParses .payableKw afterPublic
        payableMarker output) :
      ContractEntryModifiersOrdinaryParses input payableMarker output

/-- Exact ordinary constructor success, including diagnosed parameters,
discarded explicit `public`, and balanced required-body recovery. -/
inductive ConstructorDeclOrdinaryParses :
    Remainder → Syntax.ConstructorDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterParameters afterModifiers output : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterParameters
        payableMarker afterModifiers)
      (bodyParsed : IsolatedCoreBlockPublicOrdinaryParses .require
        afterModifiers body output) :
      ConstructorDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan body.span
        value := { parameters, payableMarker, body }
      } output

/-- Exact first rejecting stage of an ordinary constructor attempt.  Entry
modifiers cannot reject, so rejection occurs at the marker, parameters, or
uncaptured required body. -/
inductive ConstructorDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .constructorKw)) :
      ConstructorDeclRejects input input
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersRejected : FunctionParametersRejects afterMarker rejected) :
      ConstructorDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterModifiers rejected : Remainder}
      {parameters : DelimitedList Syntax.FunctionParameter}
      {payableMarker : Option SourceSpan} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .constructorKw)
        input markerSpan afterMarker)
      (parametersParsed : FunctionParametersOrdinaryParses afterMarker
        parameters afterParameters)
      (modifiersParsed : ContractEntryModifiersOrdinaryParses afterParameters
        payableMarker afterModifiers)
      (bodyRejected : IsolatedCoreBlockPublicRejects .require afterModifiers
        rejected) :
      ConstructorDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
