import Solcore.SourceSemantics.Context
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.SubstitutionCorrespondence
import Solcore.SourceSemantics.GraphSubstitutionProperties
import Solcore.SourceSemantics.Traits
import Solcore.SourceSemantics.Typing
import Solcore.SourceSemantics.Requirements
import Solcore.SourceSemantics.Coercions
import Solcore.SourceSemantics.Types
import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.Literals
import Solcore.SourceSemantics.Operators
import Solcore.SourceSemantics.Calls
import Solcore.SourceSemantics.Patterns
import Solcore.SourceSemantics.Places
import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Control
import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.SubstitutionProperties
import Solcore.SourceSemantics.TraitSubstitutionProperties
import Solcore.SourceSemantics.Dynamic
import Solcore.SourceSemantics.Staging

/-!
# Declarative source semantics

This umbrella exposes the proof-facing resolved-source specification.  Its
judgments validate source structure, exact generic instantiation, trait
evidence, coercions, every expression and statement form, declaration bodies,
whole programs, staging, values, heaps, primitives, patterns, and places.  No
static or staging judgment defines validity as success of an executable
frontend pass.

`Solcore.SourceSemantics.Dynamic` supplies the complete mutually recursive
successful big-step evaluation surface, positive (not total) fault
propagation, statically/staging-admitted whole-program execution, and subject reduction for
successful runs in closed structurally instantiated contexts. Structural and
trait substitution preservation close generic bodies and their evidence
without making the executable frontend authoritative.
-/
