import Solcore.Syntax.DeclarativePredicateOutcomeProperties
import Solcore.Syntax.DeclarativePredicateSequenceOutcomeGrammar

/-!
Deterministic ordinary outcomes for bare and grouped-first predicate
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- A successful bare tail has one final remainder. -/
theorem BarePredicateTailParses.output_unique
    {leftLast rightLast : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses leftLast input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses rightLast input right rightFinal
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing rightLast right rightFinal afterRight with
  | done commaAbsent =>
      cases rightParsed with
      | done => rfl
      | trailing commaParsed _ =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | next commaParsed _ _ _ =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
  | trailing commaParsed nextAbsent =>
      cases rightParsed with
      | done commaAbsent =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | trailing rightComma _ =>
          exact exactToken_output_unique commaParsed rightComma
      | next rightComma rightStarts _ _ =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact False.elim (nextAbsent rightStarts)
  | next commaParsed nextStarts predicateParsed tailParsed tailIH =>
      cases rightParsed with
      | done commaAbsent =>
          exact False.elim (absent_conflicts_exact commaAbsent commaParsed)
      | trailing rightComma rightAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact False.elim (rightAbsent nextStarts)
      | next rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          have afterPredicateEq := PredicateParses.output_unique
            predicateParsed rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- An exact bare-tail rejection excludes every successful tail. -/
theorem BarePredicateTailRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BarePredicateTailRejects input rejected)
    {lastSpan finalSpan : SourceSpan} {predicates : List Syntax.Predicate}
    {output : Remainder}
    (successful : BarePredicateTailParses lastSpan input predicates finalSpan
      output) : False := by
  induction rejection generalizing lastSpan predicates finalSpan output with
  | predicateRejected commaSpan commaParsed nextStarts predicateRejected =>
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | trailing rightComma nextAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact nextAbsent nextStarts
      | next rightComma rightStarts predicateParsed tailParsed =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact predicateDeterministicOutcomeSpec.successRejectDisjoint
            predicateRejected ⟨_, _, predicateParsed⟩
  | next commaSpan commaParsed nextStarts predicateParsed tailRejected tailIH =>
      cases successful with
      | done commaAbsent =>
          exact absent_conflicts_exact commaAbsent commaParsed
      | trailing rightComma nextAbsent =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          exact nextAbsent nextStarts
      | next rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := exactToken_output_unique commaParsed rightComma
          subst afterCommaEq
          have afterPredicateEq := PredicateParses.output_unique
            predicateParsed rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- A successful bare predicate sequence has one final remainder. -/
theorem BarePredicateSequenceParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateSequenceParses input left afterLeft)
    (rightParsed : BarePredicateSequenceParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftFirst leftTail =>
      cases rightParsed with
      | parsed rightFirst rightTail =>
          have afterFirstEq := PredicateParses.output_unique leftFirst
            rightFirst
          subst afterFirstEq
          exact leftTail.output_unique rightTail

/-- Exact bare-sequence rejection excludes every ordinary success. -/
theorem BarePredicateSequenceRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : BarePredicateSequenceRejects input rejected) :
    ¬ ∃ values output, BarePredicateSequenceParses input values output := by
  rintro ⟨values, output, successful⟩
  cases successful with
  | parsed successfulFirst successfulTail =>
      cases rejection with
      | firstRejected firstRejected =>
          exact predicateDeterministicOutcomeSpec.successRejectDisjoint
            firstRejected ⟨_, _, successfulFirst⟩
      | tailRejected rejectedFirst tailRejected =>
          have afterFirstEq := PredicateParses.output_unique rejectedFirst
            successfulFirst
          subst afterFirstEq
          exact tailRejected.disjointOrdinary successfulTail

/-- Bare predicate sequences have deterministic and exclusive outcomes. -/
theorem barePredicateSequenceDeterministicOutcomeSpec :
    DeterministicOutcomeSpec BarePredicateSequenceParses
      BarePredicateSequenceRejects where
  successOutputUnique := BarePredicateSequenceParses.output_unique
  successRejectDisjoint := BarePredicateSequenceRejects.disjointOrdinary

private theorem openingAbsent_conflicts_grouped
    {input output : Remainder}
    {values : NonemptyDelimitedList Syntax.Predicate}
    (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen))
    (parsed : GroupedPredicateSequenceParses input values output) : False := by
  unfold GroupedPredicateSequenceParses at parsed
  rcases parsed with ⟨openingSpan, first, afterFirst, rest, closingSpan,
    tokensEq, endIndexEq, openingToken, firstParsed, progress, tail,
    elementsEq, spanEq⟩
  exact openingAbsent ⟨openingSpan, openingToken⟩

/-- A prioritized predicate-sequence success has one final remainder. -/
theorem PredicateSequenceParses.output_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | bare leftUnavailable leftBare =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact leftBare.output_unique rightBare
      | grouped rightGrouped =>
          exact False.elim (leftUnavailable ⟨_, _, rightGrouped⟩)
  | grouped leftGrouped =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact False.elim (rightUnavailable ⟨_, _, leftGrouped⟩)
      | grouped rightGrouped =>
          exact leftGrouped.output_unique rightGrouped

/-- Exact predicate-sequence rejection excludes every prioritized success. -/
theorem PredicateSequenceRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : PredicateSequenceRejects input rejected) :
    ¬ ∃ values output, PredicateSequenceParses input values output := by
  rintro ⟨values, output, successful⟩
  cases rejection with
  | direct openingAbsent bareRejected =>
      cases successful with
      | bare groupedUnavailable bareParsed =>
          exact bareRejected.disjointOrdinary ⟨_, _, bareParsed⟩
      | grouped groupedParsed =>
          exact openingAbsent_conflicts_grouped openingAbsent groupedParsed
  | fallback openingPresent groupedRejected bareRejected =>
      cases successful with
      | bare groupedUnavailable bareParsed =>
          exact bareRejected.disjointOrdinary ⟨_, _, bareParsed⟩
      | grouped groupedParsed =>
          exact groupedRejected.disjointOrdinary ⟨_, _, groupedParsed⟩

/-- Grouped-first predicate sequences have deterministic exact outcomes. -/
theorem predicateSequenceDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PredicateSequenceParses PredicateSequenceRejects
    where
  successOutputUnique := PredicateSequenceParses.output_unique
  successRejectDisjoint := PredicateSequenceRejects.disjointOrdinary

end Solcore.Syntax.DeclarativeGrammar
