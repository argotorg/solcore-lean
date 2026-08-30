import Solcore.Semantics.WorldStateDelta

/-! Endpoint laws for exact, queryable WorldState transitions. -/

set_option autoImplicit false

namespace Solcore.Semantics.WorldStateDelta

/-- The indexed endpoint worlds admit exactly one WorldStateDelta value. -/
theorem unique
    {initialWorld finalWorld : WorldState}
    (left right : WorldStateDelta initialWorld finalWorld) :
    left = right := by
  cases left
  cases right
  rfl

@[simp] theorem accountEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).accountEndpoints address =
      (initialWorld.account? address, finalWorld.account? address) := by
  rfl

@[simp] theorem storageEndpoints_exact
    (initialWorld finalWorld : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (WorldStateDelta.exact (initialWorld := initialWorld)
      (finalWorld := finalWorld)).storageEndpoints address slot =
      (initialWorld.readStorage? address slot,
        finalWorld.readStorage? address slot) := by
  rfl

@[simp] theorem accountEndpoints_identity
    (world : WorldState)
    (address : Address) :
    (identity world).accountEndpoints address =
      (world.account? address, world.account? address) := by
  rfl

@[simp] theorem storageEndpoints_identity
    (world : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (identity world).storageEndpoints address slot =
      (world.readStorage? address slot, world.readStorage? address slot) := by
  rfl

@[simp] theorem slotChange?_identity
    (world : WorldState)
    (address : Address)
    (slot : Core.Word) :
    (identity world).slotChange? address slot = none := by
  simp [slotChange?, storageEndpoints]

theorem slotChange?_eq_none_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word) :
    delta.slotChange? address slot = none ↔
      (delta.storageEndpoints address slot).1 =
        (delta.storageEndpoints address slot).2 := by
  simp [slotChange?]

theorem slotChange?_eq_some_iff
    {initialWorld finalWorld : WorldState}
    (delta : WorldStateDelta initialWorld finalWorld)
    (address : Address)
    (slot : Core.Word)
    (before after : Option Core.Word) :
    delta.slotChange? address slot = some (before, after) ↔
      (delta.storageEndpoints address slot).1 = before ∧
      (delta.storageEndpoints address slot).2 = after ∧
      before ≠ after := by
  unfold slotChange?
  by_cases same :
      (delta.storageEndpoints address slot).1 =
        (delta.storageEndpoints address slot).2
  · simp [same]
    intro beforeEq afterEq
    exact beforeEq.symm.trans afterEq
  · simp only [if_neg same, Option.some.injEq]
    constructor
    · intro endpointsEq
      have beforeEq :
          (delta.storageEndpoints address slot).1 = before :=
        congrArg Prod.fst endpointsEq
      have afterEq :
          (delta.storageEndpoints address slot).2 = after :=
        congrArg Prod.snd endpointsEq
      refine ⟨beforeEq, afterEq, ?_⟩
      intro valuesEqual
      apply same
      exact beforeEq.trans (valuesEqual.trans afterEq.symm)
    · rintro ⟨beforeEq, afterEq, _different⟩
      apply Prod.ext
      · exact beforeEq
      · exact afterEq

end Solcore.Semantics.WorldStateDelta
