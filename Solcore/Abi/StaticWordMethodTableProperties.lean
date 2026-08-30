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

/-- Permuting metadata input only permutes its canonical indexed entries. -/
theorem canonicalMethodEntries_perm_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    (canonicalMethodEntries firstMethods).Perm
      (canonicalMethodEntries secondMethods) :=
  (canonicalMethodEntries_perm firstMethods).trans <|
    (inputPermutation.map Method.index).trans <|
      (canonicalMethodEntries_perm secondMethods).symm

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

namespace MethodTable

private theorem eq_of_signature_eq_of_mem
    {entries : List IndexedMethod}
    (unique : entries.Pairwise fun left right =>
      left.signature ≠ right.signature)
    {left right : IndexedMethod}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries)
    (signatureEq : left.signature = right.signature) : left = right := by
  induction entries with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember <;>
        rcases rightMember with rfl | rightMember
      · rfl
      · exact (unique.1 right rightMember signatureEq).elim
      · exact (unique.1 left leftMember signatureEq.symm).elim
      · exact inductionHypothesis unique.2 leftMember rightMember

/-- Validation success exposes the complete canonical entry list. -/
theorem entries_eq_canonical
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries = canonicalMethodEntries methods := by
  simp only [MethodTable.validate] at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · split at accepted
      · cases accepted
      · rename_i first rest entriesEq duplicateEq collisionEq
        injection accepted with tableEq
        rw [← tableEq]
        exact entriesEq.symm

/-- Every accepted entry is an indexed input method. -/
theorem entries_provenance
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table)
    {entry : IndexedMethod} (member : entry ∈ table.entries) :
    ∃ method, method ∈ methods ∧ Method.index method = entry := by
  apply mem_canonicalMethodEntries_iff.mp
  rw [← entries_eq_canonical accepted]
  exact member

/-- Accepted entries retain the indexed input multiset exactly. -/
theorem entries_perm_input
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Perm (methods.map Method.index) := by
  rw [entries_eq_canonical accepted]
  exact canonicalMethodEntries_perm methods

/-- An accepted table is nonempty. -/
theorem entries_nonempty (table : MethodTable) : table.entries ≠ [] :=
  table.nonempty

/-- Accepted signatures are pairwise unique. -/
theorem signatures_pairwise (table : MethodTable) :
    table.entries.Pairwise fun left right =>
      left.signature ≠ right.signature :=
  (firstDuplicateSignature?_eq_none_iff table.entries).mp
    table.noDuplicateSignature

/-- Accepted selectors are pairwise unique. -/
theorem selectors_pairwise (table : MethodTable) :
    table.entries.Pairwise fun left right => left.selector ≠ right.selector :=
  (firstSelectorCollision?_eq_none_iff table.entries).mp
    table.noSelectorCollision

/-- Accepted entries remain in canonical signature order. -/
theorem entries_sorted
    {methods : List Method} {table : MethodTable}
    (accepted : MethodTable.validate methods = .ok table) :
    table.entries.Pairwise fun left right =>
      IndexedMethod.signatureLE left right = true := by
  rw [entries_eq_canonical accepted]
  exact canonicalMethodEntries_sorted methods

/-- Successful canonical tables are exactly invariant under input permutation. -/
theorem entries_eq_of_input_perm
    {firstMethods secondMethods : List Method}
    {firstTable secondTable : MethodTable}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable)
    (secondAccepted : MethodTable.validate secondMethods = .ok secondTable) :
    firstTable.entries = secondTable.entries := by
  have entriesPermutation : firstTable.entries.Perm secondTable.entries :=
    (entries_perm_input firstAccepted).trans <|
      (inputPermutation.map Method.index).trans <|
        (entries_perm_input secondAccepted).symm
  apply List.Perm.eq_of_pairwise
      (le := fun left right => IndexedMethod.signatureLE left right = true)
      _ (entries_sorted firstAccepted) (entries_sorted secondAccepted)
      entriesPermutation
  intro left right leftMember rightMember forward backward
  have comparisonEq : compare left.signature right.signature = .eq :=
    Std.OrientedCmp.isLE_antisymm (cmp := compare) forward backward
  have signatureEq : left.signature = right.signature :=
    Std.LawfulEqCmp.eq_of_compare comparisonEq
  exact eq_of_signature_eq_of_mem (signatures_pairwise firstTable)
    leftMember (entriesPermutation.symm.subset rightMember) signatureEq

end MethodTable

end Solcore.Abi.V1
