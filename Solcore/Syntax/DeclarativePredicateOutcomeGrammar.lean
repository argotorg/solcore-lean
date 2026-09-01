import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar

/-!
Parser-independent exact rejection traces for predicates and grouped predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact first rejected stage of one trait-predicate attempt. -/
inductive PredicateRejects : Remainder → Remainder → Prop where
  | subjectRejected {input rejected : Remainder}
      (subjectRejected : TypeExprRejects input rejected) :
      PredicateRejects input rejected
  | colonMissing {input afterSubject : Remainder}
      {subject : Syntax.TypeExpr}
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonAbsent : TokenKindAbsentAt afterSubject.tokens
        afterSubject.endIndex afterSubject.cursor (.symbol .colon)) :
      PredicateRejects input afterSubject
  | nameRejected {input afterSubject afterColon rejected : Remainder}
      {subject : Syntax.TypeExpr} (colonSpan : SourceSpan)
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonParsed : ExactTokenParses (.symbol .colon) afterSubject colonSpan
        afterColon)
      (nameRejected : IdentifierRejects afterColon rejected) :
      PredicateRejects input rejected
  | argumentsRejected
      {input afterSubject afterColon afterName rejected : Remainder}
      {subject : Syntax.TypeExpr} {traitName : Syntax.Identifier}
      (colonSpan : SourceSpan)
      (subjectParsed : TypeExprParses input subject afterSubject)
      (colonParsed : ExactTokenParses (.symbol .colon) afterSubject colonSpan
        afterColon)
      (nameParsed : IdentifierParses afterColon traitName afterName)
      (argumentsRejected : NamedTypeArgumentsRejects TypeExprRejects afterName
        rejected) :
      PredicateRejects input rejected

/-- Exact ordinary rejection of the required nonempty grouped predicate list. -/
abbrev GroupedPredicateSequenceRejects :=
  DelimitedListRejects .leftParen .rightParen false true PredicateParses
    PredicateRejects

end Solcore.Syntax.DeclarativeGrammar
