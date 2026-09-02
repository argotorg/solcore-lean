import Solcore.Syntax.DeclarativeContractBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for contract declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad contract declaration success in executable stage order. -/
inductive ContractDeclOrdinaryParses :
    Remainder → Syntax.ContractDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics output : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      {bodySpan : SourceSpan} {members : List Syntax.ContractMember}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (bodyParsed : ContractBodyOrdinaryParses afterGenerics bodySpan members
        output) :
      ContractDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := { name, genericParameters, bodySpan, members }
      } output

/-- Exact first rejecting stage of one broad contract declaration attempt. -/
inductive ContractDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .contractKw)) :
      ContractDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      ContractDeclRejects input rejected
  | genericsRejected
      {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsRejected : OptionalGenericParametersRejects afterName
        rejected) :
      ContractDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterGenerics rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Option Syntax.GenericParameters}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .contractKw)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : OptionalGenericParametersParses
        afterName genericParameters afterGenerics)
      (bodyRejected : ContractBodyRejects afterGenerics rejected) :
      ContractDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
