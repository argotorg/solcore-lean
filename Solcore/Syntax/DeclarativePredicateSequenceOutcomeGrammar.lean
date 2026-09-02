import Solcore.Syntax.DeclarativePredicateOutcomeGrammar

/-!
Parser-independent exact rejection traces for bare and prioritized predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact rejection after at least one predicate in a bare sequence has
succeeded. Every recursive step retains its comma, positive type-start
lookahead, and successful predicate prefix. -/
inductive BarePredicateTailRejects : Remainder → Remainder → Prop where
  | predicateRejected
      {input afterComma rejected : Remainder} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nextStarts : TypeExprStartsAt afterComma)
      (predicateRejected : PredicateRejects afterComma rejected) :
      BarePredicateTailRejects input rejected
  | next
      {input afterComma afterPredicate rejected : Remainder}
      {predicate : Syntax.Predicate} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nextStarts : TypeExprStartsAt afterComma)
      (predicateParsed : PredicateParses afterComma predicate afterPredicate)
      (tailRejected : BarePredicateTailRejects afterPredicate rejected) :
      BarePredicateTailRejects input rejected

/-- Exact first rejection of one nonempty unparenthesized predicate sequence. -/
inductive BarePredicateSequenceRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : PredicateRejects input rejected) :
      BarePredicateSequenceRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.Predicate}
      (firstParsed : PredicateParses input first afterFirst)
      (tailRejected : BarePredicateTailRejects afterFirst rejected) :
      BarePredicateSequenceRejects input rejected

/-- Exact rejection of grouped-first predicate dispatch.

The direct branch records that grouped parsing was not attempted. The fallback
branch separately retains the grouped attempt's intermediate rejection and the
bare attempt's final rejection from the original input. -/
inductive PredicateSequenceRejects : Remainder → Remainder → Prop where
  | direct {input rejected : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (bareRejected : BarePredicateSequenceRejects input rejected) :
      PredicateSequenceRejects input rejected
  | fallback {input groupedRejected rejected : Remainder}
      (openingPresent : ∃ span, TokenAt input.tokens input.endIndex
        input.cursor { span, value := .symbol .leftParen })
      (groupedRejection : GroupedPredicateSequenceRejects input
        groupedRejected)
      (bareRejection : BarePredicateSequenceRejects input rejected) :
      PredicateSequenceRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
