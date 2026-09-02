import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for the namespace-import helper
after the outer `import` keyword has already been consumed.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad namespace-import success in executable stage order.  The
terminator includes both consumed-semicolon and diagnosed recovery success. -/
inductive NamespaceImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterStar afterAs afterAlias afterFrom afterPath output : Remainder}
      {alias : Syntax.Identifier} {path : Syntax.ModulePath}
      (starSpan asSpan fromSpan endSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (terminatorParsed : ImportTerminatorOrdinaryParses path.span afterPath
        endSpan output) :
      NamespaceImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .namespace path alias
      } output

/-- Exact first rejecting stage of one namespace-import helper attempt. -/
inductive NamespaceImportRejects : Remainder → Remainder → Prop where
  | starMissing {input : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star)) :
      NamespaceImportRejects input input
  | asMissing {input afterStar : Remainder}
      (starSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asAbsent : TokenKindAbsentAt afterStar.tokens afterStar.endIndex
        afterStar.cursor (.keyword .asKw)) :
      NamespaceImportRejects input afterStar
  | aliasRejected {input afterStar afterAs rejected : Remainder}
      (starSpan asSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasRejected : IdentifierRejects afterAs rejected) :
      NamespaceImportRejects input rejected
  | fromMissing
      {input afterStar afterAs afterAlias : Remainder}
      {alias : Syntax.Identifier} (starSpan asSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromAbsent : TokenKindAbsentAt afterAlias.tokens afterAlias.endIndex
        afterAlias.cursor (.identifier ContextualKeyword.from.spelling)) :
      NamespaceImportRejects input afterAlias
  | pathRejected
      {input afterStar afterAs afterAlias afterFrom rejected : Remainder}
      {alias : Syntax.Identifier} (starSpan asSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      NamespaceImportRejects input rejected
  | terminatorRejected
      {input afterStar afterAs afterAlias afterFrom afterPath
        rejected : Remainder}
      {alias : Syntax.Identifier} {path : Syntax.ModulePath}
      (starSpan asSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (asParsed : ExactTokenParses (.keyword .asKw) afterStar asSpan afterAs)
      (aliasParsed : IdentifierParses afterAs alias afterAlias)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterAlias fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (terminatorRejected : ImportTerminatorRejects afterPath rejected) :
      NamespaceImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
