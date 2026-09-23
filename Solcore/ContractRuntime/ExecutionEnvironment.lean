import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.CheckedCreationTemplateRegistry
import Solcore.ContractRuntime.CreationAddressPolicy

/-! Immutable registries and address derivation fixed for one execution. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

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

/--
Enable checked calls while disabling root creation. The empty template registry
makes every root creation request return the stable `unavailable` failure; the
inert address policy is consequently never consulted by creation preflight.
-/
def callsOnly
    (callRegistry : CheckedContractRegistry) : ExecutionEnvironment := {
  callRegistry := callRegistry
  creationTemplates := .empty
  creationAddressPolicy := inertCreationAddressPolicy
}

end ExecutionEnvironment

end Solcore.ContractRuntime

/-!
## Consolidated module: `Solcore.ContractRuntime.ExecutionEnvironmentProperties`
-/

/-! Exact projections for the immutable execution environment. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.ExecutionEnvironment

@[simp] theorem callsOnly_callRegistry
    (registry : CheckedContractRegistry) :
    (callsOnly registry).callRegistry = registry :=
  rfl

@[simp] theorem callsOnly_creationTemplates_lookup
    (registry : CheckedContractRegistry)
    (identifier : Core.Word) :
    (callsOnly registry).creationTemplates.lookup identifier = none :=
  rfl

@[simp] theorem inertCreationAddressPolicy_derive
    (creator : Address) (nonce : Core.Word) :
    inertCreationAddressPolicy.derive creator nonce = ⟨0, by decide⟩ :=
  rfl

@[simp] theorem callsOnly_creationAddressPolicy_derive
    (registry : CheckedContractRegistry)
    (creator : Address) (nonce : Core.Word) :
    (callsOnly registry).creationAddressPolicy.derive creator nonce =
      ⟨0, by decide⟩ :=
  rfl

end Solcore.ContractRuntime.ExecutionEnvironment
