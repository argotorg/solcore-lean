import Solcore.Syntax.Parser.PredicateOrdinaryRejectionSoundnessProperties

/-! External consumers for trait-predicate grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @PredicateParses
example := @PredicateRejects
example := @predicateDeterministicOutcomeSpec
example := @predicate_success_sound
example := @predicate_success_sound_and_validFor
example := @predicate_reject_sound
example := @predicate_ordinaryOutcome_sound

example {input next : State} {value : Predicate}
    (result : predicate input = .ok value next) :
    PredicateParses input.declarativeRemainder value
      next.declarativeRemainder :=
  predicate_success_sound result

example {input next : State} {value : Predicate}
    (inputValid : input.ValidFor)
    (result : predicate input = .ok value next) :
    PredicateParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  predicate_success_sound_and_validFor inputValid result

example {input rejected : State} {failure : Failure}
    (result : predicate input = .reject failure rejected) :
    PredicateRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  predicate_reject_sound result

example :
    DeterministicOutcomeSpec PredicateParses PredicateRejects :=
  predicateDeterministicOutcomeSpec

end Solcore.Test.SyntaxParserPredicateSoundnessProperties
