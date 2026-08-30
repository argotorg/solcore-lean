import Solcore.Oracle.V5.ContractAdmission

/-! Exact uniqueness and lookup laws for admitted Oracle v5 packages. -/

set_option autoImplicit false

namespace Solcore.Oracle.V5.ContractAdmission

/-- Identifier scan success is exactly pairwise identifier uniqueness. -/
theorem firstDuplicateEntryId?_eq_none_iff (entries : List AdmittedEntry) :
    firstDuplicateEntryId? entries = none ↔
      entries.Pairwise fun left right => left.id ≠ right.id := by
  induction entries with
  | nil => simp [firstDuplicateEntryId?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later => decide (later.id = first.id)) with
      | none =>
          have headDistinct : ∀ later ∈ rest, first.id ≠ later.id := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateEntryId?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.id = first.id := by
            simpa using List.find?_some found
          simp only [firstDuplicateEntryId?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

/-- Program scan success is exactly pairwise checked-Program uniqueness. -/
theorem firstDuplicateProgram?_eq_none_iff (entries : List AdmittedEntry) :
    firstDuplicateProgram? entries = none ↔
      entries.Pairwise fun left right => left.program ≠ right.program := by
  induction entries with
  | nil => simp [firstDuplicateProgram?]
  | cons first rest inductionHypothesis =>
      cases found : rest.find? (fun later =>
          decide (later.program = first.program)) with
      | none =>
          have headDistinct : ∀ later ∈ rest,
              first.program ≠ later.program := by
            intro later member equal
            have rejected := (List.find?_eq_none.mp found) later member
            exact rejected (by simp [equal])
          rw [firstDuplicateProgram?, found, inductionHypothesis,
            List.pairwise_cons]
          exact ⟨fun tail => ⟨headDistinct, tail⟩, fun all => all.2⟩
      | some later =>
          have laterMember : later ∈ rest :=
            List.mem_of_find?_eq_some found
          have equal : later.program = first.program := by
            simpa using List.find?_some found
          simp only [firstDuplicateProgram?, found, reduceCtorEq,
            false_iff, List.pairwise_cons]
          intro pairwise
          exact pairwise.1 later laterMember equal.symm

namespace ContractPackage

/-- Every sealed package has pairwise distinct validated identifiers. -/
theorem identifiersPairwise (package : ContractPackage) :
    package.entries.Pairwise fun left right => left.id ≠ right.id :=
  (firstDuplicateEntryId?_eq_none_iff package.entries).mp
    package.identifiersUnique

/-- Every sealed package has one canonical ID for each checked Program. -/
theorem programsPairwise (package : ContractPackage) :
    package.entries.Pairwise fun left right =>
      left.program ≠ right.program :=
  (firstDuplicateProgram?_eq_none_iff package.entries).mp
    package.programsUnique

private theorem findId?_of_mem
    {entries : List AdmittedEntry}
    (unique : entries.Pairwise fun left right => left.id ≠ right.id)
    {entry : AdmittedEntry}
    (member : entry ∈ entries) :
    entries.find? (fun candidate => decide (candidate.id = entry.id)) =
      some entry := by
  induction entries with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      have memberCases : entry = first ∨ entry ∈ rest := by
        simpa using member
      rcases memberCases with equal | member
      · simp [equal]
      · have different : first.id ≠ entry.id :=
          unique.1 entry member
        rw [List.find?_cons]
        simp [different, inductionHypothesis unique.2 member]

private theorem findProgram?_of_mem
    {entries : List AdmittedEntry}
    (unique : entries.Pairwise fun left right =>
      left.program ≠ right.program)
    {entry : AdmittedEntry}
    (member : entry ∈ entries) :
    entries.find? (fun candidate =>
      decide (candidate.program = entry.program)) = some entry := by
  induction entries with
  | nil => simp at member
  | cons first rest inductionHypothesis =>
      rw [List.pairwise_cons] at unique
      have memberCases : entry = first ∨ entry ∈ rest := by
        simpa using member
      rcases memberCases with equal | member
      · simp [equal]
      · have different : first.program ≠ entry.program :=
          unique.1 entry member
        rw [List.find?_cons]
        simp [different, inductionHypothesis unique.2 member]

/-- Lookup is complete for every entry carried by the finite package. -/
@[simp] theorem lookupEntry?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookupEntry? entry.id = some entry := by
  exact findId?_of_mem package.identifiersPairwise member

/-- Runnable lookup returns the exact checked contract of every package entry. -/
@[simp] theorem lookup?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookup? entry.id = some entry.contract := by
  simp [lookup?, lookupEntry?_of_mem package member]

/-- Raw validated-ID lookup has the same exact completeness law. -/
@[simp] theorem lookupRaw?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.lookupRaw? entry.id.value = some entry.contract := by
  simp [lookupRaw?, lookup?_of_mem package member]

/-- Program reverse lookup returns the unique package identifier. -/
@[simp] theorem idByProgram?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.idByProgram? entry.program = some entry.id := by
  simp [idByProgram?, findProgram?_of_mem package.programsPairwise member]

/-- Checked-code reverse lookup returns the unique package identifier. -/
@[simp] theorem idByCode?_of_mem
    (package : ContractPackage)
    {entry : AdmittedEntry}
    (member : entry ∈ package.entries) :
    package.idByCode? entry.contract.code = some entry.id := by
  exact idByProgram?_of_mem package member

/-- A successful forward lookup always round-trips through checked code. -/
theorem idByCode?_of_lookupEntry?_eq_some
    {package : ContractPackage}
    {id : ContractId}
    {entry : AdmittedEntry}
    (found : package.lookupEntry? id = some entry) :
    package.idByCode? entry.contract.code = some id := by
  rw [idByCode?_of_mem package
    (mem_of_lookupEntry?_eq_some found),
    id_eq_of_lookupEntry?_eq_some found]

end ContractPackage

end Solcore.Oracle.V5.ContractAdmission
