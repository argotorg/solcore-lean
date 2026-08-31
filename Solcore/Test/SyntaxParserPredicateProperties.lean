import Solcore.Syntax.Parser.PredicateSequenceProperties

/-! External compile consumers for canonical predicate contracts. -/

set_option autoImplicit false

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.Parser

example := predicate_validFor
example := predicate_preservesTokenWindow
example := predicate_preservesTokensOnSuccess
example := predicate_cursorMonotoneOnSuccess
example := predicate_startsAtCurrentTokenOnSuccess
example := PredicateInternals.barePredicates_validFor
example := PredicateInternals.barePredicates_preservesTokenWindow
example := PredicateInternals.barePredicates_preservesTokensOnSuccess
example := PredicateInternals.barePredicates_cursorMonotoneOnSuccess
example := PredicateInternals.groupedPredicates_validFor
example := PredicateInternals.groupedPredicates_preservesTokenWindow
example := PredicateInternals.groupedPredicates_preservesTokensOnSuccess
example := PredicateInternals.groupedPredicates_cursorMonotoneOnSuccess
example := PredicateInternals.predicateSequence_validFor
example := PredicateInternals.predicateSequence_preservesTokenWindow
example := PredicateInternals.predicateSequence_preservesTokensOnSuccess
example := PredicateInternals.predicateSequence_cursorMonotoneOnSuccess

end Tests
