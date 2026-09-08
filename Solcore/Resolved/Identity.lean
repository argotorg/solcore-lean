import Solcore.Workspace.Syntax

/-! Stable structured identities for resolved declarations and local binders.
Source spelling and spans are deliberately not part of these identities. -/

set_option autoImplicit false

namespace Solcore.Resolved

structure DeclarationId where
  moduleId : Workspace.ModuleId
  declarationIndex : Nat
  deriving Repr, DecidableEq

structure LocalId where
  owner : DeclarationId
  binderIndex : Nat
  deriving Repr, DecidableEq

end Solcore.Resolved
