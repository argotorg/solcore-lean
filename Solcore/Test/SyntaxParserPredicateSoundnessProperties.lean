import Solcore.Syntax.Parser.PredicateSoundnessProperties

/-! External consumers for trait-predicate grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @PredicateParses
example := @predicate_success_sound
example := @predicate_success_sound_and_validFor

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

end Solcore.Test.SyntaxParserPredicateSoundnessProperties
