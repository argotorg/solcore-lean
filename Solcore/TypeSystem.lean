import Solcore.TypeSystem.Type
import Solcore.TypeSystem.Substitution
import Solcore.TypeSystem.Unification
import Solcore.TypeSystem.Scheme
import Solcore.TypeSystem.Inference

/-!
Executable source-level types, substitutions, rank-1 schemes and first-order
inference.  This layer remains separate from the closed monomorphic Core type
language until specialization.
-/
