import Solcore.Abi.StaticWordMethodTable

/-! External proof contract for deterministic Static Word method tables. -/

set_option autoImplicit false

namespace Solcore.Abi.V1

/-- A duplicate-signature scan succeeds exactly when every pair differs. -/
theorem firstDuplicateSignature?_eq_none_iff (entries : List IndexedMethod) :
    firstDuplicateSignature? entries = none ↔
      entries.Pairwise fun left right => left.signature ≠ right.signature := by
  induction entries with
  | nil => simp [firstDuplicateSignature?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.signature = first.signature)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.signature ≠ later.signature := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateSignature?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.signature = first.signature := by
            simpa using List.find?_some found
          simp only [firstDuplicateSignature?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

/-- A selector-collision scan succeeds exactly when every pair differs. -/
theorem firstSelectorCollision?_eq_none_iff (entries : List IndexedMethod) :
    firstSelectorCollision? entries = none ↔
      entries.Pairwise fun left right => left.selector ≠ right.selector := by
  induction entries with
  | nil => simp [firstSelectorCollision?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.selector = first.selector)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.selector ≠ later.selector := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstSelectorCollision?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.selector = first.selector := by
            simpa using List.find?_some found
          simp only [firstSelectorCollision?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

theorem IndexedMethod.signatureLE_trans
    {first second third : IndexedMethod}
    (firstSecond : IndexedMethod.signatureLE first second = true)
    (secondThird : IndexedMethod.signatureLE second third = true) :
    IndexedMethod.signatureLE first third = true := by
  exact Std.TransCmp.isLE_trans (cmp := compare) firstSecond secondThird

theorem IndexedMethod.signatureLE_total (left right : IndexedMethod) :
    IndexedMethod.signatureLE left right = true ∨
      IndexedMethod.signatureLE right left = true := by
  cases order : compare left.signature right.signature with
  | lt => exact Or.inl (by simp [IndexedMethod.signatureLE, order])
  | eq => exact Or.inl (by simp [IndexedMethod.signatureLE, order])
  | gt =>
      have swapped : compare right.signature left.signature = .lt :=
        Std.OrientedCmp.lt_of_gt (cmp := compare) order
      exact Or.inr (by simp [IndexedMethod.signatureLE, swapped])

/-- Canonicalization retains exactly the indexed input entries. -/
theorem canonicalMethodEntries_perm (methods : List Method) :
    (canonicalMethodEntries methods).Perm (methods.map Method.index) := by
  exact List.mergeSort_perm _ _

/-- Pointwise provenance for every canonical entry. -/
theorem mem_canonicalMethodEntries_iff
    {methods : List Method} {entry : IndexedMethod} :
    entry ∈ canonicalMethodEntries methods ↔
      ∃ method, method ∈ methods ∧ Method.index method = entry := by
  simp [canonicalMethodEntries]

/-- Canonical entries are nondecreasing by signature. -/
theorem canonicalMethodEntries_sorted (methods : List Method) :
    (canonicalMethodEntries methods).Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true := by
  unfold canonicalMethodEntries
  apply List.pairwise_mergeSort
  · intro first second third firstSecond secondThird
    exact IndexedMethod.signatureLE_trans firstSecond secondThird
  · intro left right
    rcases IndexedMethod.signatureLE_total left right with forward | backward
    · simp [forward]
    · simp [backward]

end Solcore.Abi.V1
