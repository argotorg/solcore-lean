import Solcore.SourceSemantics.Context
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Traits
import Solcore.SourceSemantics.Typing

/-!
# Declarative source semantics

This umbrella exposes the proof-facing source-language specification.  Its
judgments validate source structure, generic instantiations, trait evidence,
and resolved references without defining validity as success of the executable
frontend checker.

The current layer is intentionally a foundation rather than a claim of full
language coverage.  Expression, statement, declaration-body, and whole-program
typing judgments build on these modules.
-/
