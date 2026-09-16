import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.RequirementProperties
import Solcore.Frontend.SourceInference.StateProperties
import Solcore.Frontend.SourceInference.TypedIR
import Solcore.Frontend.SourceInference.TypedIRProperties

/-!
Executable source-connected type inference.

The implementation is split into shared types, resolution policy, canonical
expression/body inference, and public whole-program entry points.
-/
