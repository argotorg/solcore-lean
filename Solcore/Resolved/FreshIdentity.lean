import Solcore.Resolved.Identity

/-! Fresh local identities relative to one explicit scope. This does not choose
a declaration traversal order or promise freshness outside the supplied scope. -/

set_option autoImplicit false

namespace Solcore.Resolved

private def freshBinderIndex (owner : DeclarationId) : List LocalId → Nat
  | [] => 0
  | id :: scope =>
      if id.owner = owner then max (id.binderIndex + 1) (freshBinderIndex owner scope)
      else freshBinderIndex owner scope

/-- Select index zero for an empty same-owner scope, otherwise one past its
greatest binder index. Other declaration owners do not affect the choice. -/
def freshLocalId (owner : DeclarationId) (scope : List LocalId) : LocalId :=
  { owner, binderIndex := freshBinderIndex owner scope }

theorem freshLocalId_owner (owner : DeclarationId) (scope : List LocalId) :
    (freshLocalId owner scope).owner = owner := rfl

theorem freshLocalId_empty (owner : DeclarationId) :
    freshLocalId owner [] = { owner, binderIndex := 0 } := rfl

/-- Every existing binder of this owner has strictly smaller index. -/
theorem lt_freshLocalId_binderIndex {owner : DeclarationId} {scope : List LocalId}
    {id : LocalId} (member : id ∈ scope) (sameOwner : id.owner = owner) :
    id.binderIndex < (freshLocalId owner scope).binderIndex := by
  change id.binderIndex < freshBinderIndex owner scope
  induction scope with
  | nil => cases member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with same | member
      · subst head
        simp only [freshBinderIndex, if_pos sameOwner]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · have tailBound := ih member
        by_cases headOwner : head.owner = owner
        · simp only [freshBinderIndex, if_pos headOwner]
          exact Nat.lt_of_lt_of_le tailBound (Nat.le_max_right _ _)
        · simpa only [freshBinderIndex, if_neg headOwner] using tailBound

theorem freshLocalId_not_mem (owner : DeclarationId) (scope : List LocalId) :
    freshLocalId owner scope ∉ scope := by
  intro member
  exact Nat.lt_irrefl _ (lt_freshLocalId_binderIndex member (freshLocalId_owner owner scope))

/-- Allocating again after extending the scope advances the chosen index by one. -/
theorem freshLocalId_cons_fresh_binderIndex (owner : DeclarationId) (scope : List LocalId) :
    (freshLocalId owner (freshLocalId owner scope :: scope)).binderIndex =
      (freshLocalId owner scope).binderIndex + 1 := by
  simp only [freshLocalId, freshBinderIndex, ↓reduceIte]
  exact Nat.max_eq_left (Nat.le_succ _)

theorem freshLocalId_cons_fresh_ne (owner : DeclarationId) (scope : List LocalId) :
    freshLocalId owner (freshLocalId owner scope :: scope) ≠ freshLocalId owner scope := by
  intro same
  have member : freshLocalId owner (freshLocalId owner scope :: scope) ∈
      freshLocalId owner scope :: scope := by rw [same]; exact List.mem_cons_self
  exact freshLocalId_not_mem owner _ member

theorem freshLocalId_cons_of_ne_owner (owner : DeclarationId) (scope : List LocalId)
    (id : LocalId) (different : id.owner ≠ owner) :
    freshLocalId owner (id :: scope) = freshLocalId owner scope := by
  simp only [freshLocalId, freshBinderIndex, if_neg different]

/-- Allocation is independent of scope ordering, even with repeated identities. -/
theorem freshLocalId_eq_of_perm (owner : DeclarationId) {left right : List LocalId}
    (permutation : left.Perm right) : freshLocalId owner left = freshLocalId owner right := by
  suffices indices : freshBinderIndex owner left = freshBinderIndex owner right by
    simp only [freshLocalId, indices]
  induction permutation with
  | nil => rfl
  | cons id _ ih => simp only [freshBinderIndex, ih]
  | swap first second rest =>
      by_cases firstOwner : first.owner = owner <;>
        by_cases secondOwner : second.owner = owner <;>
        simp [freshBinderIndex, firstOwner, secondOwner, Nat.max_left_comm]
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH

/-- Relabeling owners injectively preserves the exact allocated index for any
scope. Indices are unchanged; the owner map need not be surjective. -/
theorem freshLocalId_map_owner (mapping : DeclarationId → DeclarationId)
    (injective : Function.Injective mapping) (owner : DeclarationId) (scope : List LocalId) :
    freshLocalId (mapping owner)
        (scope.map (fun id => ⟨mapping id.owner, id.binderIndex⟩)) =
      ⟨mapping owner, (freshLocalId owner scope).binderIndex⟩ := by
  suffices indices : freshBinderIndex (mapping owner)
      (scope.map (fun id => ⟨mapping id.owner, id.binderIndex⟩)) = freshBinderIndex owner scope by
    exact congrArg (LocalId.mk (mapping owner)) indices
  induction scope with
  | nil => rfl
  | cons id rest ih =>
      simp only [List.map_cons, freshBinderIndex, injective.eq_iff, ih]

end Solcore.Resolved
