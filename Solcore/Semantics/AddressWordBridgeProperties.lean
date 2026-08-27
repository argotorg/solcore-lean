import Solcore.Semantics.AddressWordBridge

/-! Focused laws for the strict internal address and word bridge. -/

set_option autoImplicit false

namespace Solcore.Semantics

theorem wordToAddress?_eq_some_iff
    (word : Core.Word) (address : Address) :
    wordToAddress? word = some address ↔ word.val = address.val := by
  unfold wordToAddress?
  split
  next inRange =>
    constructor
    · intro equal
      have payloadEqual : (⟨word.val, inRange⟩ : Address) = address :=
        Option.some.inj equal
      exact congrArg Fin.val payloadEqual
    · intro valuesEqual
      apply congrArg some
      exact Fin.ext valuesEqual
  next outOfRange =>
    constructor
    · intro impossible
      cases impossible
    · intro valuesEqual
      have inRange : word.val < addressModulus :=
        Eq.mp
          (congrArg (fun value => value < addressModulus) valuesEqual.symm)
          address.isLt
      exact (outOfRange inRange).elim

theorem wordToAddress?_success_iff (word : Core.Word) :
    (∃ address : Address, wordToAddress? word = some address) ↔
      word.val < addressModulus := by
  constructor
  · rintro ⟨address, success⟩
    have valuesEqual :=
      (wordToAddress?_eq_some_iff word address).mp success
    exact Eq.mp
      (congrArg (fun value => value < addressModulus) valuesEqual.symm)
      address.isLt
  · intro inRange
    let address : Address := ⟨word.val, inRange⟩
    exact ⟨address, (wordToAddress?_eq_some_iff word address).mpr rfl⟩

@[simp] theorem wordToAddress?_failure_iff (word : Core.Word) :
    wordToAddress? word = none ↔ addressModulus ≤ word.val := by
  unfold wordToAddress?
  split
  next inRange =>
    constructor
    · intro impossible
      cases impossible
    · intro outOfRange
      exact (Nat.not_lt_of_ge outOfRange inRange).elim
  next outOfRange =>
    constructor
    · intro _
      exact Nat.le_of_not_gt outOfRange
    · intro _
      rfl

@[simp] theorem wordToAddress?_addressToWord (address : Address) :
    wordToAddress? (addressToWord address) = some address := by
  unfold wordToAddress? addressToWord
  split
  next inRange =>
    apply congrArg some
    exact Fin.ext rfl
  next outOfRange =>
    exact (outOfRange address.isLt).elim

theorem addressToWord_of_wordToAddress?_eq_some
    {word : Core.Word} {address : Address}
    (success : wordToAddress? word = some address) :
    addressToWord address = word := by
  apply Fin.ext
  exact ((wordToAddress?_eq_some_iff word address).mp success).symm

theorem addressToWord_injective : Function.Injective addressToWord := by
  intro left right equal
  apply Fin.ext
  change left.val = right.val
  exact congrArg (fun word : Core.Word => word.val) equal

end Solcore.Semantics
