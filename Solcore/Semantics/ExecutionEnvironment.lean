import Solcore.Semantics.CheckedContractRegistry
import Solcore.Semantics.CheckedCreationTemplateRegistry
import Solcore.Semantics.CreationAddressPolicy

/-! Immutable registries and address derivation fixed for one execution. -/

set_option autoImplicit false

namespace Solcore.Semantics

/-- Every external capability whose replacement could change execution meaning. -/
structure ExecutionEnvironment where
  callRegistry : CheckedContractRegistry
  creationTemplates : CheckedCreationTemplateRegistry
  creationAddressPolicy : CreationAddressPolicy

namespace ExecutionEnvironment

/-- A deterministic inert policy for executions that cannot create contracts. -/
def inertCreationAddressPolicy : CreationAddressPolicy := {
  derive := fun _creator _nonce => ⟨0, by decide⟩
}

/-- Preserve the existing calls-only scheduler boundary with no templates. -/
def callsOnly
    (callRegistry : CheckedContractRegistry) : ExecutionEnvironment := {
  callRegistry := callRegistry
  creationTemplates := .empty
  creationAddressPolicy := inertCreationAddressPolicy
}

end ExecutionEnvironment

end Solcore.Semantics
