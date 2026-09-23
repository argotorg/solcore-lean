import Solcore.ContractRuntime.CheckedCreationPreflight
set_option autoImplicit false
namespace Solcore.ContractRuntime
namespace RegisteredCreationRuntime

@[simp] theorem validate?_lookup_none (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (h : e.callRegistry.lookup a = none) :
    validate? e a t = none := by
  unfold validate?; split
  · rfl
  · simp_all

@[simp] theorem validate?_program_mismatch (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (c : CheckedCoreContract)
    (hl : e.callRegistry.lookup a = some c)
    (hp : c.code.program ≠ t.runtime.code.program) : validate? e a t = none := by
  unfold validate?; split
  · simp_all
  · rename_i found heq
    have : found = c := Option.some.inj (heq.symm.trans hl)
    subst found
    simp [hp]

theorem validate?_some_program_eq (e : ExecutionEnvironment) (a : Address)
    (t : CheckedCreationTemplate) (r : RegisteredCreationRuntime e a t)
    (_h : validate? e a t = some r) :
    r.contract.code.program = t.runtime.code.program := r.program_eq
end RegisteredCreationRuntime

namespace CheckedCreationPreflight
@[simp] theorem prepare_templateUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (h : e.creationTemplates.lookup id = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · rfl
  · simp_all

@[simp] theorem prepare_creatorUnavailable (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = none) :
    prepare s e creator id value = .error .unavailable := by
  unfold prepare; split
  · simp_all
  · rename_i actual heq
    have : actual = t := Option.some.inj (heq.symm.trans ht)
    subst actual
    split <;> simp_all

@[simp] theorem prepare_nonceOverflow (s : WorldState)
    (e : ExecutionEnvironment) (creator : Address) (id value : Core.Word)
    (t : CheckedCreationTemplate) (account : Account)
    (ht : e.creationTemplates.lookup id = some t)
    (ha : s.account? creator = some account)
    (ho : account.incrementNonce? = none) :
    prepare s e creator id value = .error .nonceOverflow := by
  unfold prepare; split
  · simp_all
  · rename_i actualT teq
    have : actualT = t := Option.some.inj (teq.symm.trans ht); subst actualT
    split
    · simp_all
    · rename_i actualA aeq
      have : actualA = account := Option.some.inj (aeq.symm.trans ha); subst actualA
      split <;> simp_all

theorem PreparedCheckedCreation.runtime_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.runtimeRegistration.contract = p.template.runtime := p.runtimeRegistration.contract_eq

theorem PreparedCheckedCreation.address_exact
    {s : WorldState} {e : ExecutionEnvironment} {creator : Address}
    {id value : Core.Word} (p : PreparedCheckedCreation s e creator id value) :
    p.statePreparation.createdAddress =
      e.creationAddressPolicy.derive creator p.oldNonce := by
  rw [p.preparation_address_eq, p.createdAddress_eq]
end CheckedCreationPreflight
end Solcore.ContractRuntime
