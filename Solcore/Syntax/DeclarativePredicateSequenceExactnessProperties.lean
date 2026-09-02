import Solcore.Syntax.DeclarativePredicateExactnessProperties
import Solcore.Syntax.DeclarativePredicateSequenceOutcomeProperties

/-! Exact bare and prioritized predicate-sequence outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem predicateSequence_absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (present : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, present⟩

private theorem predicateSequence_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  predicateSequence_absent_conflicts_token absent parsed.1

/-- With the preceding span fixed, a bare predicate tail fixes its elements,
final span, and remainder. -/
theorem BarePredicateTailParses.result_unique
    {lastSpan : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses lastSpan input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses lastSpan input right rightFinal
      afterRight) :
    left = right ∧ leftFinal = rightFinal ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right rightFinal afterRight with
  | done leftCommaAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl, rfl⟩
      | trailing rightComma _ =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact leftCommaAbsent
              rightComma)
      | next rightComma _ _ _ =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact leftCommaAbsent
              rightComma)
  | trailing leftComma leftNextAbsent =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact rightCommaAbsent
              leftComma)
      | trailing rightComma rightNextAbsent =>
          rcases leftComma.result_unique rightComma with
            ⟨commaSpanEq, afterCommaEq⟩
          exact ⟨rfl, commaSpanEq, afterCommaEq⟩
      | next rightComma rightNextStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim (leftNextAbsent rightNextStarts)
  | next leftComma leftNextStarts leftPredicate leftTail tailIH =>
      cases rightParsed with
      | done rightCommaAbsent =>
          exact False.elim
            (predicateSequence_absent_conflicts_exact rightCommaAbsent
              leftComma)
      | trailing rightComma rightNextAbsent =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim (rightNextAbsent leftNextStarts)
      | next rightComma rightNextStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          rcases predicateExactOutcomeSpec.successResultUnique leftPredicate
              rightPredicate with ⟨predicateEq, afterPredicateEq⟩
          subst predicateEq
          subst afterPredicateEq
          rcases tailIH rightTail with ⟨tailEq, finalEq, outputEq⟩
          subst tailEq
          exact ⟨rfl, finalEq, outputEq⟩

/-- With the preceding span fixed, a bare predicate tail fixes its values. -/
theorem BarePredicateTailParses.value_unique
    {lastSpan : SourceSpan} {input : Remainder}
    {left right : List Syntax.Predicate}
    {leftFinal rightFinal : SourceSpan}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateTailParses lastSpan input left leftFinal
      afterLeft)
    (rightParsed : BarePredicateTailParses lastSpan input right rightFinal
      afterRight) : left = right :=
  (leftParsed.result_unique rightParsed).1

/-- A bare predicate tail has one first rejecting endpoint. -/
theorem BarePredicateTailRejects.output_unique
    {input left right : Remainder}
    (leftRejected : BarePredicateTailRejects input left)
    (rightRejected : BarePredicateTailRejects input right) : left = right := by
  induction leftRejected generalizing right with
  | predicateRejected leftCommaSpan leftComma leftStarts leftPredicate =>
      cases rightRejected with
      | predicateRejected rightCommaSpan rightComma rightStarts
          rightPredicate =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact predicateExactOutcomeSpec.rejectOutputUnique leftPredicate
            rightPredicate
      | next rightCommaSpan rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim
            (predicateExactOutcomeSpec.successRejectDisjoint leftPredicate
              ⟨_, _, rightPredicate⟩)
  | next leftCommaSpan leftComma leftStarts leftPredicate leftTail tailIH =>
      cases rightRejected with
      | predicateRejected rightCommaSpan rightComma rightStarts
          rightPredicate =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          exact False.elim
            (predicateExactOutcomeSpec.successRejectDisjoint rightPredicate
              ⟨_, _, leftPredicate⟩)
      | next rightCommaSpan rightComma rightStarts rightPredicate rightTail =>
          have afterCommaEq := leftComma.output_unique rightComma
          subst afterCommaEq
          have afterPredicateEq :=
            predicateExactOutcomeSpec.successOutputUnique leftPredicate
              rightPredicate
          subst afterPredicateEq
          exact tailIH rightTail

/-- A complete bare predicate sequence fixes its nonempty AST. -/
theorem BarePredicateSequenceParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : BarePredicateSequenceParses input left afterLeft)
    (rightParsed : BarePredicateSequenceParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftFirst leftTail =>
      cases rightParsed with
      | parsed rightFirst rightTail =>
          rcases predicateExactOutcomeSpec.successResultUnique leftFirst
              rightFirst with ⟨firstEq, afterFirstEq⟩
          subst firstEq
          subst afterFirstEq
          rcases leftTail.result_unique rightTail with
            ⟨tailEq, finalSpanEq, outputEq⟩
          subst tailEq
          subst finalSpanEq
          rfl

/-- Bare predicate-sequence rejection has one endpoint. -/
theorem BarePredicateSequenceRejects.output_unique
    {input left right : Remainder}
    (leftRejected : BarePredicateSequenceRejects input left)
    (rightRejected : BarePredicateSequenceRejects input right) :
    left = right := by
  cases leftRejected <;> cases rightRejected <;>
    grind [predicateExactOutcomeSpec.successOutputUnique,
      predicateExactOutcomeSpec.successRejectDisjoint,
      predicateExactOutcomeSpec.rejectOutputUnique,
      BarePredicateTailRejects.output_unique]

/-- Bare predicate sequences have exact outcomes. -/
theorem barePredicateSequenceExactOutcomeSpec :
    ExactDeterministicOutcomeSpec BarePredicateSequenceParses
      BarePredicateSequenceRejects where
  toDeterministicOutcomeSpec := barePredicateSequenceDeterministicOutcomeSpec
  successValueUnique := BarePredicateSequenceParses.value_unique
  rejectOutputUnique := BarePredicateSequenceRejects.output_unique

/-- Prioritized grouped-or-bare predicate success fixes its AST. -/
theorem PredicateSequenceParses.value_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | bare leftUnavailable leftBare =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.successValueUnique
            leftBare rightBare
      | grouped rightGrouped =>
          exact False.elim (leftUnavailable ⟨_, _, rightGrouped⟩)
  | grouped leftGrouped =>
      cases rightParsed with
      | bare rightUnavailable rightBare =>
          exact False.elim (rightUnavailable ⟨_, _, leftGrouped⟩)
      | grouped rightGrouped =>
          exact groupedPredicateSequenceExactOutcomeSpec.successValueUnique
            leftGrouped rightGrouped

/-- Prioritized predicate-sequence rejection has one endpoint. -/
theorem PredicateSequenceRejects.output_unique
    {input left right : Remainder}
    (leftRejected : PredicateSequenceRejects input left)
    (rightRejected : PredicateSequenceRejects input right) : left = right := by
  cases leftRejected with
  | direct leftOpeningAbsent leftBare =>
      cases rightRejected with
      | direct rightOpeningAbsent rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftBare rightBare
      | fallback rightOpeningPresent rightGrouped rightBare =>
          rcases rightOpeningPresent with ⟨span, openingToken⟩
          exact False.elim
            (predicateSequence_absent_conflicts_token leftOpeningAbsent
              openingToken)
  | fallback leftOpeningPresent leftGrouped leftBare =>
      cases rightRejected with
      | direct rightOpeningAbsent rightBare =>
          rcases leftOpeningPresent with ⟨span, openingToken⟩
          exact False.elim
            (predicateSequence_absent_conflicts_token rightOpeningAbsent
              openingToken)
      | fallback rightOpeningPresent rightGrouped rightBare =>
          exact barePredicateSequenceExactOutcomeSpec.rejectOutputUnique
            leftBare rightBare

/-- Prioritized grouped-or-bare predicate sequences have exact outcomes. -/
theorem predicateSequenceExactOutcomeSpec :
    ExactDeterministicOutcomeSpec PredicateSequenceParses
      PredicateSequenceRejects where
  toDeterministicOutcomeSpec := predicateSequenceDeterministicOutcomeSpec
  successValueUnique := PredicateSequenceParses.value_unique
  rejectOutputUnique := PredicateSequenceRejects.output_unique

/-- A complete prioritized predicate sequence fixes its AST and remainder. -/
theorem PredicateSequenceParses.result_unique
    {input : Remainder}
    {left right : NonemptyDelimitedList Syntax.Predicate}
    {afterLeft afterRight : Remainder}
    (leftParsed : PredicateSequenceParses input left afterLeft)
    (rightParsed : PredicateSequenceParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  predicateSequenceExactOutcomeSpec.successResultUnique leftParsed rightParsed

end Solcore.Syntax.DeclarativeGrammar
