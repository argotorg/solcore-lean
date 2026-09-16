import Solcore.Frontend.SourceInference.Program
import Solcore.Frontend.SourceInference.RequirementProperties

/-!
Executable source-connected type inference.

The implementation is split into shared types, resolution policy, canonical
expression/body inference, and public whole-program entry points.
-/
