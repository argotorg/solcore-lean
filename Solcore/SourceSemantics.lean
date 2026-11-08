import Solcore.SourceSemantics.Context
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Instantiation
import Solcore.SourceSemantics.Internal.Substitution.Unification
import Solcore.SourceSemantics.Graph
import Solcore.SourceSemantics.Traits
import Solcore.SourceSemantics.TraitResolutionSoundness
import Solcore.SourceSemantics.Typing
import Solcore.SourceSemantics.Requirements
import Solcore.SourceSemantics.Types
import Solcore.SourceSemantics.Binders
import Solcore.SourceSemantics.Expressions
import Solcore.SourceSemantics.Ownership
import Solcore.SourceSemantics.Control
import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.StaticValidation
import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.ProgramCheckingSoundness
import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws
import Solcore.SourceSemantics.Internal.Substitution.TraitLaws
import Solcore.SourceSemantics.Internal.Inference.Soundness
import Solcore.SourceSemantics.Internal.Inference.ExpressionInduction
import Solcore.SourceSemantics.SourceProgramCheckingSoundness
import Solcore.SourceSemantics.InferenceSoundness
import Solcore.SourceSemantics.Dynamic
import Solcore.SourceSemantics.Staging
import Solcore.SourceSemantics.SourceStageAnalysisSoundness

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
successful runs in structurally instantiated contexts whose rigid and lexical
flexible binders are closed while residual inference admission remains open. Structural and
trait substitution preservation close generic bodies and their evidence
without making the executable frontend authoritative.

## Reading order

1. **Static semantics.** `Context`, `Types`, `Binders`, then `Expressions` and `Static`, which
   assembles the construct rules. `Program` ends with `ProgramWellFormed`.
2. **Dynamic semantics.** `Dynamic.Value`, `Dynamic.Heap`, `Dynamic.Evaluation` and `Dynamic.Fault`.
3. **Source type preservation.** The statement is in `Dynamic.Preservation`, and the proof in
   `Dynamic.WholeLanguagePreservation`.
4. **Staging.** `Staging.Classification`, `Staging.RecursiveProfile`, `Staging.Erasure` and
   `Staging.Preservation`.
5. **The executable frontend.** `SourceProgramCheckingSoundness`, then `InferenceSoundness`.
6. **Actual compilation.** `CompiledBodies`.

## Main theorems

- `ProgramWellFormed.wholeLanguagePreservation`, in `Dynamic.WholeLanguagePreservation`.
- `Dynamic.ProgramEvaluates.preserves`, in `Dynamic.Program`.
- `programWellFormed_ofCheckProgram_statements`, in `SourceProgramCheckingSoundness`.
- `SourceInferenceSoundness.programWellFormed_ofCheckProgram_inferStatementsFuel_sound`, in
  `InferenceSoundness`. Its premise is the recursive soundness of statement inference.
- `SourceCompiledActualInitializerBarriers.compile_cached_bodies`, in `CompiledBodies`.

The reviewer's guide is `docs/review/source-semantics.md`.
-/
