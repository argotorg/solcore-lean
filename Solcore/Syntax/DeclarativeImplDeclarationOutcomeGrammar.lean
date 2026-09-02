import Solcore.Syntax.DeclarativeGenericParametersOutcomeGrammar
import Solcore.Syntax.DeclarativeImplBodyOutcomeGrammar
import Solcore.Syntax.DeclarativeImplDefaultMarkerOutcomeGrammar
import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar
import Solcore.Syntax.DeclarativeWhereClauseOutcomeGrammar

/-! Parser-independent broad ordinary outcomes for implementation declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad implementation declaration in executable stage order. -/
inductive ImplDeclOrdinaryParses :
    Remainder → Syntax.ImplDecl → Remainder → Prop where
  | parsed
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        afterWhere output : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      {whereClause : Option Syntax.WhereClause} {bodySpan : SourceSpan}
      {methods : List Syntax.ImplMethod}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereParsed : OptionalWhereClauseParses afterArguments whereClause
        afterWhere)
      (bodyParsed : ImplBodyOrdinaryParses afterWhere bodySpan methods
        output) :
      ImplDeclOrdinaryParses input {
        span := SourceSpan.cover (defaultMarker.getD markerSpan) bodySpan
        value := {
          defaultMarker
          genericParameters
          traitName
          headArguments
          whereClause
          bodySpan
          methods
        }
      } output

/-- Exact first rejecting stage after the infallible optional-default prefix. -/
inductive ImplDeclRejects : Remainder → Remainder → Prop where
  | markerMissing {input afterDefault : Remainder}
      {defaultMarker : Option SourceSpan}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerAbsent : TokenKindAbsentAt afterDefault.tokens
        afterDefault.endIndex afterDefault.cursor
        (.identifier ContextualKeyword.impl.spelling)) :
      ImplDeclRejects input afterDefault
  | genericsRejected {input afterDefault afterMarker rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsRejected : OptionalGenericParametersRejects afterMarker
        rejected) :
      ImplDeclRejects input rejected
  | nameRejected
      {input afterDefault afterMarker afterGenerics rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameRejected : IdentifierRejects afterGenerics rejected) :
      ImplDeclRejects input rejected
  | argumentsRejected
      {input afterDefault afterMarker afterGenerics afterName rejected :
        Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsRejected : ImplHeadArgumentsRejects afterName rejected) :
      ImplDeclRejects input rejected
  | whereRejected
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereRejected : OptionalWhereClauseRejects afterArguments rejected) :
      ImplDeclRejects input rejected
  | bodyRejected
      {input afterDefault afterMarker afterGenerics afterName afterArguments
        afterWhere rejected : Remainder}
      {defaultMarker : Option SourceSpan}
      {genericParameters : Option Syntax.GenericParameters}
      {traitName : Syntax.Identifier}
      {headArguments : NonemptyDelimitedList Syntax.TypeExpr}
      {whereClause : Option Syntax.WhereClause}
      (defaultParsed : OptionalImplDefaultMarkerOrdinaryParses input
        defaultMarker afterDefault)
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.impl.spelling)
        afterDefault markerSpan afterMarker)
      (genericsParsed : OptionalGenericParametersParses afterMarker
        genericParameters afterGenerics)
      (nameParsed : IdentifierParses afterGenerics traitName afterName)
      (argumentsParsed : ImplHeadArgumentsOrdinaryParses afterName
        headArguments afterArguments)
      (whereParsed : OptionalWhereClauseParses afterArguments whereClause
        afterWhere)
      (bodyRejected : ImplBodyRejects afterWhere rejected) :
      ImplDeclRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
