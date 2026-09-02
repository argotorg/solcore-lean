import Solcore.Syntax.Parser.PredicateSequenceOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WhereClauseOrdinaryRejectionSoundnessProperties

/-! External consumers for exact predicate-sequence and optional-where outcomes. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserWhereClauseSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TypeExprStartToken
example := @TypeExprStartsAt
example := @TypeExprAbsentAt
example := @BarePredicateTailParses
example := @BarePredicateTailRejects
example := @BarePredicateSequenceParses
example := @BarePredicateSequenceRejects
example := @barePredicateSequenceDeterministicOutcomeSpec
example := @barePredicateSequenceExactOutcomeSpec
example := @GroupedPredicateSequenceParses
example := @GroupedPredicateSequenceUnavailable
example := @GroupedPredicateSequenceRejects
example := @groupedPredicateSequenceDeterministicOutcomeSpec
example := @groupedPredicateSequenceExactOutcomeSpec
example := @GroupedPredicateSequenceRejects.no_parse
example := @PredicateSequenceParses
example := @PredicateSequenceRejects
example := @predicateSequenceDeterministicOutcomeSpec
example := @predicateSequenceExactOutcomeSpec
example := @OptionalWhereClauseParses
example := @OptionalWhereClauseRejects
example := @optionalWhereClauseDeterministicOutcomeSpec
example := @optionalWhereClauseExactOutcomeSpec

example := @PredicateInternals.barePredicates_success_sound
example := @PredicateInternals.barePredicates_success_sound_and_validFor
example := @PredicateInternals.barePredicates_reject_sound
example := @PredicateInternals.barePredicates_ordinaryOutcome_sound
example := @PredicateInternals.barePredicates_exactOutcomeSpec
example := @PredicateInternals.barePredicates_success_result_unique
example := @PredicateInternals.barePredicates_reject_output_unique
example := @PredicateInternals.groupedPredicates_success_sound
example := @PredicateInternals.groupedPredicates_success_sound_and_validFor
example := @PredicateInternals.groupedPredicates_reject_sound
example := @PredicateInternals.groupedPredicates_ordinaryOutcome_sound
example := @PredicateInternals.groupedPredicates_exactOutcomeSpec
example := @PredicateInternals.groupedPredicates_success_result_unique
example := @PredicateInternals.groupedPredicates_reject_output_unique
example := @PredicateInternals.predicateSequence_success_sound
example := @PredicateInternals.predicateSequence_success_sound_and_validFor
example := @PredicateInternals.predicateSequence_reject_sound
example := @PredicateInternals.predicateSequence_ordinaryOutcome_sound
example := @PredicateInternals.predicateSequence_exactOutcomeSpec
example := @PredicateInternals.predicateSequence_success_result_unique
example := @PredicateInternals.predicateSequence_reject_output_unique
example := @whereClause_success_sound
example := @whereClause_success_sound_and_validFor
example := @whereClause_reject_sound
example := @whereClause_ordinaryOutcome_sound
example := @whereClause_exactOutcomeSpec
example := @whereClause_success_result_unique
example := @whereClause_reject_output_unique

example {input next : State}
    {predicates : NonemptyDelimitedList Predicate}
    (result : PredicateInternals.predicateSequence input =
      .ok predicates next) :
    PredicateSequenceParses input.declarativeRemainder predicates
      next.declarativeRemainder :=
  PredicateInternals.predicateSequence_success_sound result

example {input next : State}
    {predicates : NonemptyDelimitedList Predicate}
    (inputValid : input.ValidFor)
    (result : PredicateInternals.predicateSequence input =
      .ok predicates next) :
    PredicateSequenceParses input.declarativeRemainder predicates
        next.declarativeRemainder ∧
      NonemptyDelimitedList.ValidFor Predicate.ValidFor input.file
        predicates :=
  PredicateInternals.predicateSequence_success_sound_and_validFor inputValid
    result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.groupedPredicates input =
      .reject failure rejected) :
    GroupedPredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.groupedPredicates_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.barePredicates input =
      .reject failure rejected) :
    BarePredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.barePredicates_reject_sound result

example {input rejected : State} {failure : Failure}
    (result : PredicateInternals.predicateSequence input =
      .reject failure rejected) :
    PredicateSequenceRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  PredicateInternals.predicateSequence_reject_sound result

example {input rejected : Remainder}
    (rejection : GroupedPredicateSequenceRejects input rejected) :
    GroupedPredicateSequenceUnavailable input :=
  rejection.no_parse

example :
    DeterministicOutcomeSpec GroupedPredicateSequenceParses
      GroupedPredicateSequenceRejects :=
  groupedPredicateSequenceDeterministicOutcomeSpec

example {input next : State} {clause : Option WhereClause}
    (result : whereClause input = .ok clause next) :
    OptionalWhereClauseParses input.declarativeRemainder clause
      next.declarativeRemainder :=
  whereClause_success_sound result

example {input next : State} {clause : Option WhereClause}
    (inputValid : input.ValidFor)
    (result : whereClause input = .ok clause next) :
    OptionalWhereClauseParses input.declarativeRemainder clause
        next.declarativeRemainder ∧
      Option.ValidFor WhereClause.ValidFor input.file clause :=
  whereClause_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : whereClause input = .reject failure rejected) :
    OptionalWhereClauseRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  whereClause_reject_sound result

end Solcore.Test.SyntaxParserWhereClauseSoundnessProperties
