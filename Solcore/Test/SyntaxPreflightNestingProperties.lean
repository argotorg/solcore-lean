import Solcore.Syntax.Parser.Nesting

/-! External consumers for nesting-diagnostic provenance. -/

namespace Tests

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @NestingContext
example := @NestingDimension
example := @NestingOverflow
example := @NestingScans
example := @NestingOutcome
example := @NestingClears
example := @NestingExceeds
example := @NestingScans.result_unique
example := @NestingScans.exists_result
example := @NestingExceeds.disjointClears
example := @NestingExceeds.overflow_unique
example := @nestingOutcome_total
example := @nestingOverflowDiagnostic
example := @checkNesting_eq_map_of_outcome
example := @checkNesting_reflects_outcome
example := @checkNesting_none_iff_nestingClears
example := @checkNesting_some_iff_nestingExceeds
example := @checkNesting_ordinaryOutcome_sound
example := @checkNesting_some_span_validFor
example := @checkNesting_lexed_some_span_validFor

end Tests
