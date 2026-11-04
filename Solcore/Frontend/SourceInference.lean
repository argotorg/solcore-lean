import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.Internal.ExpressionProperties
import Solcore.Frontend.SourceInference.Internal.ProgramProperties
import Solcore.Frontend.SourceInference.Internal.RequirementProperties
import Solcore.Frontend.SourceInference.Internal.StateProperties
import Solcore.Frontend.SourceInference.TypedIR
import Solcore.Frontend.SourceInference.Internal.TypedIRProperties

/-!
# Source inference

Executable type inference over source. Read `SourceInference/TypedIR`, then `Types`, `Resolution`,
`Expression` and `Program`. `SourceInference/Internal/` holds the proofs.
-/

/-!
Executable source-connected type inference.

The implementation is split into shared types, resolution policy, canonical
expression/body inference, and public whole-program entry points.
-/
