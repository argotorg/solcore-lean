import Solcore.Syntax.Parser.PredicateSequenceTotalityProperties

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserPredicateSequenceTotalityProperties

open Solcore.Syntax.Parser

example := @predicate_invariantFreeOnValid
example := @predicate_ordinary
example := @predicate_elementTotalityContract
example := @PredicateInternals.barePredicatesTail_ordinary_of_remainingCount_lt
example := @PredicateInternals.barePredicatesTail_ne_invariant_of_remainingCount_lt
example := @PredicateInternals.barePredicatesTail_production_ordinary
example := @PredicateInternals.barePredicates_ordinary
example := @PredicateInternals.barePredicates_invariantFreeOnValid
example := @PredicateInternals.groupedPredicates_ordinary
example := @PredicateInternals.groupedPredicates_invariantFreeOnValid
example := @PredicateInternals.predicateSequence_ordinary
example := @PredicateInternals.predicateSequence_invariantFreeOnValid

end Solcore.Test.SyntaxParserPredicateSequenceTotalityProperties
