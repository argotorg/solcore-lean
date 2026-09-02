import Solcore.Syntax.DeclarativeHidingClauseOutcomeGrammar
import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
import Solcore.Syntax.DeclarativeModulePathOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for wildcard import payloads.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact broad wildcard-import success in executable stage order, including
optional hiding and explicit-or-recovered terminator success. -/
inductive WildcardImportOrdinaryParses (start : SourceSpan) :
    Remainder → Syntax.ImportDecl → Remainder → Prop where
  | parsed
      {input afterStar afterFrom afterPath afterHiding output : Remainder}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      {endSpan : SourceSpan} (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorParsed : ImportTerminatorOrdinaryParses
        (match hidden with
          | some clause => clause.span
          | none => path.span)
        afterHiding endSpan output) :
      WildcardImportOrdinaryParses start input {
        span := SourceSpan.cover start endSpan
        value := .wildcard path hidden
      } output

/-- Exact first rejecting stage of one wildcard-import helper attempt. -/
inductive WildcardImportRejects : Remainder → Remainder → Prop where
  | starMissing {input : Remainder}
      (starAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .star)) :
      WildcardImportRejects input input
  | fromMissing {input afterStar : Remainder} (starSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromAbsent : TokenKindAbsentAt afterStar.tokens afterStar.endIndex
        afterStar.cursor (.identifier ContextualKeyword.from.spelling)) :
      WildcardImportRejects input afterStar
  | pathRejected {input afterStar afterFrom rejected : Remainder}
      (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathRejected : ModulePathRejects afterFrom rejected) :
      WildcardImportRejects input rejected
  | hidingRejected
      {input afterStar afterFrom afterPath rejected : Remainder}
      {path : Syntax.ModulePath} (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingRejected : OptionalHidingRejects afterPath rejected) :
      WildcardImportRejects input rejected
  | terminatorRejected
      {input afterStar afterFrom afterPath afterHiding
        rejected : Remainder}
      {path : Syntax.ModulePath} {hidden : Option Syntax.HidingClause}
      (starSpan fromSpan : SourceSpan)
      (starParsed : ExactTokenParses (.symbol .star) input starSpan afterStar)
      (fromParsed : ExactTokenParses
        (.identifier ContextualKeyword.from.spelling) afterStar fromSpan
          afterFrom)
      (pathParsed : ModulePathOrdinaryParses afterFrom path afterPath)
      (hidingParsed : OptionalHidingOrdinaryParses afterPath hidden
        afterHiding)
      (terminatorRejected : ImportTerminatorRejects afterHiding rejected) :
      WildcardImportRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
