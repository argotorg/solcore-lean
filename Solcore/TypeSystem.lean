import Solcore.TypeSystem.Type
import Solcore.TypeSystem.Substitution
import Solcore.TypeSystem.Unification
import Solcore.TypeSystem.Scheme
import Solcore.TypeSystem.Inference
import Solcore.TypeSystem.Internal.SubstitutionLaws
import Solcore.TypeSystem.Internal.SchemeLaws
import Solcore.TypeSystem.Internal.InferenceLaws

/-!
# Type system

Executable source-level types, substitutions, rank-1 schemes and first-order inference. This layer
stays separate from the closed monomorphic Core types until specialization. `docs/guide/foundations.md`
lists every file.

Read `Type`, `Substitution`, `Unification`, `Scheme` and `Inference`, in that order. Their laws are
in `Internal/`.
-/
