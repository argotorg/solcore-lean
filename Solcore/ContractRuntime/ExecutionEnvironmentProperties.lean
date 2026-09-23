import Solcore.ContractRuntime.ExecutionEnvironment

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
