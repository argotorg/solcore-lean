import Solcore.Resolved.Identity

/-! Stable identities allocated by source-connected inference. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceInference

/-- Function-local identity of one inferred trait or coercion obligation. -/
structure RequirementId where
  index : Nat
  deriving Repr, BEq, DecidableEq

/-- Identity of one source occurrence, scoped to its owning declaration. -/
structure OccurrenceId where
  owner : Resolved.DeclarationId
  index : Nat
  deriving Repr, BEq, DecidableEq

end Solcore.Frontend.SourceInference
