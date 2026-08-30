import Solcore.Semantics.TopLevelStorageDelta

/-! Exact endpoint laws for queryable top-level storage deltas. -/

set_option autoImplicit false

namespace Solcore.Semantics.TopLevelStorageDelta

theorem slotChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    delta.slotChange? slot = none ↔
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot := by
  simp [slotChange?]

theorem slotChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot before after : Core.Word) :
    delta.slotChange? slot = some (before, after) ↔
      delta.initialAccount.storageRead slot = before ∧
      delta.finalAccount.storageRead slot = after ∧
      before ≠ after := by
  unfold slotChange?
  by_cases same :
      delta.initialAccount.storageRead slot =
        delta.finalAccount.storageRead slot
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨beforeEq, afterEq⟩
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      exact ⟨beforeEq, afterEq⟩

theorem finalWorld_code?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target) :
    finalWorld.code? target = initialWorld.code? target := by
  simp [WorldState.code?, delta.initialAccount_present,
    delta.finalAccount_present, delta.code_preserved]

theorem initialWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    initialWorld.readStorage? target slot =
      some (delta.initialAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.initialAccount_present]

theorem finalWorld_readStorage?_target
    {initialWorld finalWorld : WorldState}
    {target : Address}
    (delta : TopLevelStorageDelta initialWorld finalWorld target)
    (slot : Core.Word) :
    finalWorld.readStorage? target slot =
      some (delta.finalAccount.storageRead slot) := by
  simp [WorldState.readStorage?, delta.finalAccount_present]

end Solcore.Semantics.TopLevelStorageDelta
