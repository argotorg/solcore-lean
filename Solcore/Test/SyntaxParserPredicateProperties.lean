import Solcore.Syntax.Parser.WhereClauseProperties

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
example := PredicateInternals.barePredicates_startsAtCurrentTokenOnSuccess
example := PredicateInternals.groupedPredicates_startsAtCurrentTokenOnSuccess
example := PredicateInternals.predicateSequence_startsAtCurrentTokenOnSuccess
example := whereClause_validFor
example := whereClause_preservesTokenWindow
example := whereClause_preservesTokensOnSuccess
example := whereClause_cursorMonotoneOnSuccess
example := @whereClause_some_startsAtCurrentTokenOnSuccess

end Tests
