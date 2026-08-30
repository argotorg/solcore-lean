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

private theorem pairwise_signatures_iff_of_perm
    {first second : List IndexedMethod} (permutation : first.Perm second) :
    (first.Pairwise fun left right => left.signature ≠ right.signature) ↔
      second.Pairwise fun left right => left.signature ≠ right.signature := by
  constructor
  · intro pairwise
    exact permutation.pairwise pairwise fun different equal =>
      different equal.symm
  · intro pairwise
    exact permutation.symm.pairwise pairwise fun different equal =>
      different equal.symm

private theorem pairwise_selectors_iff_of_perm
    {first second : List IndexedMethod} (permutation : first.Perm second) :
    (first.Pairwise fun left right => left.selector ≠ right.selector) ↔
      second.Pairwise fun left right => left.selector ≠ right.selector := by
  constructor
  · intro pairwise
    exact permutation.pairwise pairwise fun different equal =>
      different equal.symm
  · intro pairwise
    exact permutation.symm.pairwise pairwise fun different equal =>
      different equal.symm

/-- Duplicate-scan success is invariant under input permutation. -/
theorem duplicateScanNone_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    firstDuplicateSignature? (canonicalMethodEntries firstMethods) = none ↔
      firstDuplicateSignature? (canonicalMethodEntries secondMethods) = none := by
  rw [firstDuplicateSignature?_eq_none_iff,
    firstDuplicateSignature?_eq_none_iff]
  exact pairwise_signatures_iff_of_perm
    (canonicalMethodEntries_perm_of_input_perm inputPermutation)

/-- Selector-scan success is invariant under input permutation. -/
theorem selectorScanNone_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    firstSelectorCollision? (canonicalMethodEntries firstMethods) = none ↔
      firstSelectorCollision? (canonicalMethodEntries secondMethods) = none := by
  rw [firstSelectorCollision?_eq_none_iff,
    firstSelectorCollision?_eq_none_iff]
  exact pairwise_selectors_iff_of_perm
    (canonicalMethodEntries_perm_of_input_perm inputPermutation)

/-- Canonical emptiness is invariant under input permutation. -/
theorem canonicalEntriesNil_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    canonicalMethodEntries firstMethods = [] ↔
      canonicalMethodEntries secondMethods = [] := by
  have entriesPermutation :=
    canonicalMethodEntries_perm_of_input_perm inputPermutation
  constructor
  · intro firstNil
    rw [firstNil] at entriesPermutation
    exact entriesPermutation.nil_eq.symm
  · intro secondNil
    rw [secondNil] at entriesPermutation
    exact entriesPermutation.eq_nil

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

inductive ErrorKind where
  | empty
  | duplicateSignature
  | selectorCollision
  deriving Repr, BEq, DecidableEq

def ErrorKind.ofError : MethodTableError → ErrorKind
  | .empty => .empty
  | .duplicateSignature .. => .duplicateSignature
  | .selectorCollision .. => .selectorCollision

/-- Every rejected validation has exactly one exhaustive scan classification. -/
theorem rejected_classification
    {methods : List Method} {error : MethodTableError}
    (rejected : MethodTable.validate methods = .error error) :
    (ErrorKind.ofError error = .empty ∧
      canonicalMethodEntries methods = []) ∨
    (ErrorKind.ofError error = .duplicateSignature ∧
      canonicalMethodEntries methods ≠ [] ∧
      firstDuplicateSignature? (canonicalMethodEntries methods) ≠ none) ∨
    (ErrorKind.ofError error = .selectorCollision ∧
      canonicalMethodEntries methods ≠ [] ∧
      firstDuplicateSignature? (canonicalMethodEntries methods) = none ∧
      firstSelectorCollision? (canonicalMethodEntries methods) ≠ none) := by
  simp only [MethodTable.validate] at rejected
  split at rejected
  · rename_i entriesEq
    injection rejected with errorEq
    rw [← errorEq]
    exact Or.inl ⟨rfl, entriesEq⟩
  · split at rejected
    · rename_i first rest entriesEq conflict duplicateEq
      injection rejected with errorEq
      rw [← errorEq]
      exact Or.inr <| Or.inl ⟨rfl, by simp [entriesEq], by simp [entriesEq,
        duplicateEq]⟩
    · split at rejected
      · rename_i first rest entriesEq duplicateEq conflict collisionEq
        injection rejected with errorEq
        rw [← errorEq]
        exact Or.inr <| Or.inr ⟨rfl, by simp [entriesEq], by
          simpa [entriesEq] using duplicateEq, by simp [entriesEq,
            collisionEq]⟩
      · cases rejected

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

/-- Reordering input cannot change the validator's rejection class. -/
theorem errorKind_eq_of_input_perm
    {firstMethods secondMethods : List Method}
    {firstError secondError : MethodTableError}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstRejected : MethodTable.validate firstMethods = .error firstError)
    (secondRejected : MethodTable.validate secondMethods = .error secondError) :
    ErrorKind.ofError firstError = ErrorKind.ofError secondError := by
  have nilIff := canonicalEntriesNil_iff_of_input_perm inputPermutation
  have duplicateNoneIff :=
    duplicateScanNone_iff_of_input_perm inputPermutation
  rcases rejected_classification firstRejected with firstEmpty |
      firstDuplicate | firstCollision <;>
    rcases rejected_classification secondRejected with secondEmpty |
      secondDuplicate | secondCollision
  · exact firstEmpty.1.trans secondEmpty.1.symm
  · exact (secondDuplicate.2.1 (nilIff.mp firstEmpty.2)).elim
  · exact (secondCollision.2.1 (nilIff.mp firstEmpty.2)).elim
  · exact (firstDuplicate.2.1 (nilIff.mpr secondEmpty.2)).elim
  · exact firstDuplicate.1.trans secondDuplicate.1.symm
  · exact (firstDuplicate.2.2
      (duplicateNoneIff.mpr secondCollision.2.2.1)).elim
  · exact (firstCollision.2.1 (nilIff.mpr secondEmpty.2)).elim
  · exact (secondDuplicate.2.2
      (duplicateNoneIff.mp firstCollision.2.2.1)).elim
  · exact firstCollision.1.trans secondCollision.1.symm

/-- One successful ordering yields a successful reordered table with identical
canonical entries. -/
theorem validate_ok_of_input_perm
    {firstMethods secondMethods : List Method} {firstTable : MethodTable}
    (inputPermutation : firstMethods.Perm secondMethods)
    (firstAccepted : MethodTable.validate firstMethods = .ok firstTable) :
    ∃ secondTable,
      MethodTable.validate secondMethods = .ok secondTable ∧
      firstTable.entries = secondTable.entries := by
  have firstNonempty : canonicalMethodEntries firstMethods ≠ [] := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.nonempty
  have secondNonempty : canonicalMethodEntries secondMethods ≠ [] :=
    fun secondNil => firstNonempty
      ((canonicalEntriesNil_iff_of_input_perm inputPermutation).mpr secondNil)
  have firstDuplicateNone :
      firstDuplicateSignature? (canonicalMethodEntries firstMethods) = none := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.noDuplicateSignature
  have secondDuplicateNone :
      firstDuplicateSignature? (canonicalMethodEntries secondMethods) = none :=
    (duplicateScanNone_iff_of_input_perm inputPermutation).mp
      firstDuplicateNone
  have firstSelectorNone :
      firstSelectorCollision? (canonicalMethodEntries firstMethods) = none := by
    rw [← entries_eq_canonical firstAccepted]
    exact firstTable.noSelectorCollision
  have secondSelectorNone :
      firstSelectorCollision? (canonicalMethodEntries secondMethods) = none :=
    (selectorScanNone_iff_of_input_perm inputPermutation).mp firstSelectorNone
  cases secondEq : MethodTable.validate secondMethods with
  | ok secondTable =>
      exact ⟨secondTable, rfl,
        entries_eq_of_input_perm inputPermutation firstAccepted secondEq⟩
  | error secondError =>
      rcases rejected_classification secondEq with empty | duplicate | collision
      · exact (secondNonempty empty.2).elim
      · exact (duplicate.2.2 secondDuplicateNone).elim
      · exact (collision.2.2.2 secondSelectorNone).elim

/-- Validation acceptance is invariant under arbitrary input permutation. -/
theorem validate_accepts_iff_of_input_perm
    {firstMethods secondMethods : List Method}
    (inputPermutation : firstMethods.Perm secondMethods) :
    (∃ table, MethodTable.validate firstMethods = .ok table) ↔
      ∃ table, MethodTable.validate secondMethods = .ok table := by
  constructor
  · rintro ⟨firstTable, firstAccepted⟩
    obtain ⟨secondTable, secondAccepted, _⟩ :=
      validate_ok_of_input_perm inputPermutation firstAccepted
    exact ⟨secondTable, secondAccepted⟩
  · rintro ⟨secondTable, secondAccepted⟩
    obtain ⟨firstTable, firstAccepted, _⟩ :=
      validate_ok_of_input_perm inputPermutation.symm secondAccepted
    exact ⟨firstTable, firstAccepted⟩

end MethodTable

end Solcore.Abi.V1
