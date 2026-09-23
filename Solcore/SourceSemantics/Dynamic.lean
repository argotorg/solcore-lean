import Solcore.SourceSemantics.Dynamic.Value
import Solcore.SourceSemantics.Dynamic.Heap
import Solcore.SourceSemantics.Dynamic.Typing
import Solcore.SourceSemantics.Dynamic.Default
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.Dynamic.Control
import Solcore.SourceSemantics.Dynamic.PatternCompletenessProperties
import Solcore.SourceSemantics.Dynamic.Preservation
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.Dynamic.Program

/-!
# Declarative source dynamics

This umbrella exposes mathematical source values and heaps, exact evidence
closure, primitive operations, pattern and place behavior, and the fuel-free
successful and faulting big-step semantics for resolved expressions,
statements, calls, loops, and control-transfer forms, together with the
statically/staging-admitted whole-program entry relation and source-level preservation theorems.
Fault derivations are positive evidence rather than a total complement of
success. Whole-language preservation concerns successful runs whose rigid
parameters have been structurally instantiated and whose lexical flexible
scope is closed; the body-wide residual inference scope remains open.
-/
