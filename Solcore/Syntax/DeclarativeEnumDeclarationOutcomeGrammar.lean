import Solcore.Syntax.DeclarativeEnumBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar

/-! Parser-independent ordinary outcomes for complete enum declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary enum declarations reuse the exact grammar at one supplied derive
attribute. -/
abbrev EnumDeclOrdinaryParses
    (deriveAttribute : Option Syntax.DeriveAttribute) :=
  EnumDeclParses deriveAttribute

/-- Exact first rejecting stage of one enum-declaration attempt. -/
inductive EnumDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.enum.spelling)) :
      EnumDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      EnumDeclRejects input rejected
  | parametersRejected
      {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (parametersRejected : OptionalGenericParametersRejects afterName
        rejected) :
      EnumDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterParameters rejected : Remainder}
      {name : Syntax.Identifier}
      {parameters : Option Syntax.GenericParameters} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.enum.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (parametersParsed : OptionalGenericParametersParses afterName parameters
        afterParameters)
      (bodyRejected : EnumBodyRejects afterParameters rejected) :
      EnumDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
