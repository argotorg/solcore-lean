import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar
import Solcore.Syntax.DeclarativeTraitBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeWhereClauseOutcomeGrammar

/-! Parser-independent ordinary outcomes for complete trait declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad trait declaration in executable stage order. -/
inductive TraitDeclOrdinaryParses :
    Remainder → Syntax.TraitDecl → Remainder → Prop where
  | parsed
      {input afterMarker afterName afterGenerics afterWhere output : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters}
      {whereClause : Option Syntax.WhereClause} {bodySpan : SourceSpan}
      {methods : List Syntax.TraitMethod} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereParsed : OptionalWhereClauseParses afterGenerics whereClause
        afterWhere)
      (bodyParsed : TraitBodyOrdinaryParses afterWhere bodySpan methods
        output) :
      TraitDeclOrdinaryParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := {
          name
          genericParameters
          whereClause
          bodySpan
          methods
        }
      } output

/-- Exact first rejecting stage of one broad trait-declaration attempt. -/
inductive TraitDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.trait.spelling)) :
      TraitDeclRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameRejected : IdentifierRejects afterMarker rejected) :
      TraitDeclRejects input rejected
  | genericsRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsRejected : GenericParametersRejects afterName rejected) :
      TraitDeclRejects input rejected
  | whereRejected
      {input afterMarker afterName afterGenerics rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereRejected : OptionalWhereClauseRejects afterGenerics rejected) :
      TraitDeclRejects input rejected
  | bodyRejected
      {input afterMarker afterName afterGenerics afterWhere rejected : Remainder}
      {name : Syntax.Identifier}
      {genericParameters : Syntax.GenericParameters}
      {whereClause : Option Syntax.WhereClause} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.trait.spelling)
        input markerSpan afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (genericsParsed : GenericParametersParses afterName genericParameters
        afterGenerics)
      (whereParsed : OptionalWhereClauseParses afterGenerics whereClause
        afterWhere)
      (bodyRejected : TraitBodyRejects afterWhere rejected) :
      TraitDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
