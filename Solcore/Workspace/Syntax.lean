import Solcore.Workspace.Path

set_option autoImplicit false

namespace Solcore.Workspace

/-- One caller-supplied source record before workspace validation. -/
structure RawSourceFile where
  path : String
  content : String
  deriving Repr, BEq, DecidableEq

namespace RawSourceFile

/-- The UTF-8 content bytes charged to this source record. -/
def sourceBytes (file : RawSourceFile) : Nat :=
  file.content.utf8ByteSize

end RawSourceFile

/-- One named external library before workspace validation. -/
structure RawExternalLibrary where
  name : String
  sources : List RawSourceFile
  deriving Repr, BEq, DecidableEq

namespace RawExternalLibrary

/-- The number of caller-supplied source records in this library declaration. -/
def sourceFiles (library : RawExternalLibrary) : Nat :=
  library.sources.length

/-- The UTF-8 content bytes charged to this library declaration. -/
def sourceBytes (library : RawExternalLibrary) : Nat :=
  (library.sources.map RawSourceFile.sourceBytes).sum

end RawExternalLibrary

/-- The complete caller-supplied workspace before structural validation. -/
structure RawWorkspace where
  entry : String
  mainSources : List RawSourceFile
  externalLibraries : List RawExternalLibrary
  deriving Repr, BEq, DecidableEq

namespace RawWorkspace

/-- The number of caller-supplied main and external source records. -/
def sourceFiles (workspace : RawWorkspace) : Nat :=
  workspace.mainSources.length +
    (workspace.externalLibraries.map RawExternalLibrary.sourceFiles).sum

/-- The UTF-8 content bytes in caller-supplied main and external sources. -/
def sourceBytes (workspace : RawWorkspace) : Nat :=
  (workspace.mainSources.map RawSourceFile.sourceBytes).sum +
    (workspace.externalLibraries.map RawExternalLibrary.sourceBytes).sum

end RawWorkspace

/-- The logical library namespace that owns a source or module. -/
inductive LibraryId where
  | main
  | standard
  | external (name : ExternalLibraryName)
  deriving Repr, BEq, DecidableEq

namespace LibraryId

private def orderKey : LibraryId → Option (Option ExternalLibraryName)
  | .main => none
  | .standard => some none
  | .external name => some (some name)

/-- Canonical library order: main, standard, then external names. -/
def compare : LibraryId → LibraryId → Ordering
  | .main, .main => .eq
  | .main, _ => .lt
  | .standard, .main => .gt
  | .standard, .standard => .eq
  | .standard, .external _ => .lt
  | .external _, .main
  | .external _, .standard => .gt
  | .external left, .external right => ExternalLibraryName.compare left right

private theorem compare_eq_orderKey_compare (left right : LibraryId) :
    LibraryId.compare left right =
      Ord.compare (orderKey left) (orderKey right) := by
  cases left <;> cases right <;> rfl

instance : Ord LibraryId where
  compare := LibraryId.compare

instance : Std.OrientedCmp LibraryId.compare where
  eq_swap {a b} := by
    rw [compare_eq_orderKey_compare, compare_eq_orderKey_compare]
    exact Std.OrientedOrd.eq_swap

instance : Std.TransCmp LibraryId.compare where
  eq_swap := Std.OrientedCmp.eq_swap
  isLE_trans {a b c} hab hbc := by
    rw [compare_eq_orderKey_compare] at hab hbc ⊢
    exact Std.TransOrd.isLE_trans hab hbc

instance : Std.OrientedOrd LibraryId := by
  change Std.OrientedCmp LibraryId.compare
  infer_instance

instance : Std.TransOrd LibraryId := by
  change Std.TransCmp LibraryId.compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : LibraryId} :
    LibraryId.compare left right = .eq ↔ left = right := by
  cases left <;> cases right <;>
    simp [LibraryId.compare]

instance : Std.LawfulEqCmp LibraryId.compare where
  compare_self := Std.ReflCmp.compare_self
  eq_of_compare := LibraryId.compare_eq_iff_eq.mp

instance : Std.LawfulEqOrd LibraryId := by
  change Std.LawfulEqCmp LibraryId.compare
  infer_instance

/-- Non-strict canonical library comparison for deterministic sorting. -/
def le (left right : LibraryId) : Bool :=
  (LibraryId.compare left right).isLE

instance : LE LibraryId where
  le left right := LibraryId.le left right = true

theorem le_refl (value : LibraryId) : LibraryId.le value value = true := by
  exact Std.ReflCmp.isLE_rfl (cmp := LibraryId.compare)

theorem le_trans {a b c : LibraryId}
    (hab : LibraryId.le a b = true) (hbc : LibraryId.le b c = true) :
    LibraryId.le a c = true := by
  exact Std.TransCmp.isLE_trans (cmp := LibraryId.compare) hab hbc

theorem le_total (left right : LibraryId) :
    LibraryId.le left right = true ∨ LibraryId.le right left = true := by
  cases order : LibraryId.compare left right with
  | lt => exact Or.inl (by simp [LibraryId.le, order])
  | eq => exact Or.inl (by simp [LibraryId.le, order])
  | gt =>
      apply Or.inr
      have swapped : LibraryId.compare right left = .lt :=
        Std.OrientedCmp.lt_of_gt (cmp := LibraryId.compare) order
      simp [LibraryId.le, swapped]

theorem le_antisymm {left right : LibraryId}
    (forward : LibraryId.le left right = true)
    (backward : LibraryId.le right left = true) :
    left = right := by
  apply LibraryId.compare_eq_iff_eq.mp
  exact Std.OrientedCmp.isLE_antisymm (cmp := LibraryId.compare)
    forward backward

end LibraryId

/-- Structured identity of one source in a logical library. -/
structure SourceId where
  library : LibraryId
  path : CanonicalSourcePath
  deriving Repr, BEq, DecidableEq

/-- Structured identity of one module in a logical library. -/
structure ModuleId where
  library : LibraryId
  path : ModulePath
  deriving Repr, BEq, DecidableEq

namespace ModuleId

/-- Canonical module order by library and then logical path. -/
def compare (left right : ModuleId) : Ordering :=
  compareLex (compareOn ModuleId.library) (compareOn ModuleId.path) left right

instance : Ord ModuleId where
  compare := ModuleId.compare

instance : Std.OrientedCmp ModuleId.compare := by
  unfold ModuleId.compare
  infer_instance

instance : Std.TransCmp ModuleId.compare := by
  unfold ModuleId.compare
  infer_instance

instance : Std.OrientedOrd ModuleId := by
  change Std.OrientedCmp ModuleId.compare
  infer_instance

instance : Std.TransOrd ModuleId := by
  change Std.TransCmp ModuleId.compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : ModuleId} :
    ModuleId.compare left right = .eq ↔ left = right := by
  cases left
  cases right
  simp [ModuleId.compare, compareLex_eq_eq, compareOn]

instance : Std.LawfulEqCmp ModuleId.compare where
  compare_self := Std.ReflCmp.compare_self
  eq_of_compare := ModuleId.compare_eq_iff_eq.mp

instance : Std.LawfulEqOrd ModuleId := by
  change Std.LawfulEqCmp ModuleId.compare
  infer_instance

/-- Non-strict canonical module comparison for deterministic sorting. -/
def le (left right : ModuleId) : Bool :=
  (ModuleId.compare left right).isLE

instance : LE ModuleId where
  le left right := ModuleId.le left right = true

theorem le_refl (value : ModuleId) : ModuleId.le value value = true := by
  exact Std.ReflCmp.isLE_rfl (cmp := ModuleId.compare)

theorem le_trans {a b c : ModuleId}
    (hab : ModuleId.le a b = true) (hbc : ModuleId.le b c = true) :
    ModuleId.le a c = true := by
  exact Std.TransCmp.isLE_trans (cmp := ModuleId.compare) hab hbc

theorem le_total (left right : ModuleId) :
    ModuleId.le left right = true ∨ ModuleId.le right left = true := by
  cases order : ModuleId.compare left right with
  | lt => exact Or.inl (by simp [ModuleId.le, order])
  | eq => exact Or.inl (by simp [ModuleId.le, order])
  | gt =>
      apply Or.inr
      have swapped : ModuleId.compare right left = .lt :=
        Std.OrientedCmp.lt_of_gt (cmp := ModuleId.compare) order
      simp [ModuleId.le, swapped]

theorem le_antisymm {left right : ModuleId}
    (forward : ModuleId.le left right = true)
    (backward : ModuleId.le right left = true) :
    left = right := by
  apply ModuleId.compare_eq_iff_eq.mp
  exact Std.OrientedCmp.isLE_antisymm (cmp := ModuleId.compare)
    forward backward

end ModuleId

namespace SourceId

/-- Removes only the source suffix wrapper while preserving logical ownership. -/
def toModuleId (source : SourceId) : ModuleId := {
  library := source.library
  path := source.path.modulePath
}

/-- Canonical source order by library and then canonical source path. -/
def compare (left right : SourceId) : Ordering :=
  compareLex (compareOn SourceId.library) (compareOn SourceId.path) left right

instance : Ord SourceId where
  compare := SourceId.compare

instance : Std.OrientedCmp SourceId.compare := by
  unfold SourceId.compare
  infer_instance

instance : Std.TransCmp SourceId.compare := by
  unfold SourceId.compare
  infer_instance

instance : Std.OrientedOrd SourceId := by
  change Std.OrientedCmp SourceId.compare
  infer_instance

instance : Std.TransOrd SourceId := by
  change Std.TransCmp SourceId.compare
  infer_instance

@[simp] theorem compare_eq_iff_eq {left right : SourceId} :
    SourceId.compare left right = .eq ↔ left = right := by
  cases left
  cases right
  simp [SourceId.compare, compareLex_eq_eq, compareOn]

instance : Std.LawfulEqCmp SourceId.compare where
  compare_self := Std.ReflCmp.compare_self
  eq_of_compare := SourceId.compare_eq_iff_eq.mp

instance : Std.LawfulEqOrd SourceId := by
  change Std.LawfulEqCmp SourceId.compare
  infer_instance

/-- Non-strict canonical source comparison for deterministic sorting. -/
def le (left right : SourceId) : Bool :=
  (SourceId.compare left right).isLE

instance : LE SourceId where
  le left right := SourceId.le left right = true

theorem le_refl (value : SourceId) : SourceId.le value value = true := by
  exact Std.ReflCmp.isLE_rfl (cmp := SourceId.compare)

theorem le_trans {a b c : SourceId}
    (hab : SourceId.le a b = true) (hbc : SourceId.le b c = true) :
    SourceId.le a c = true := by
  exact Std.TransCmp.isLE_trans (cmp := SourceId.compare) hab hbc

theorem le_total (left right : SourceId) :
    SourceId.le left right = true ∨ SourceId.le right left = true := by
  cases order : SourceId.compare left right with
  | lt => exact Or.inl (by simp [SourceId.le, order])
  | eq => exact Or.inl (by simp [SourceId.le, order])
  | gt =>
      apply Or.inr
      have swapped : SourceId.compare right left = .lt :=
        Std.OrientedCmp.lt_of_gt (cmp := SourceId.compare) order
      simp [SourceId.le, swapped]

theorem le_antisymm {left right : SourceId}
    (forward : SourceId.le left right = true)
    (backward : SourceId.le right left = true) :
    left = right := by
  apply SourceId.compare_eq_iff_eq.mp
  exact Std.OrientedCmp.isLE_antisymm (cmp := SourceId.compare)
    forward backward

/-- Removing the source suffix wrapper does not merge source identities. -/
theorem toModuleId_injective : Function.Injective toModuleId := by
  intro left right equality
  cases left with
  | mk leftLibrary leftPath =>
      cases right with
      | mk rightLibrary rightPath =>
          cases leftPath with
          | mk leftModulePath =>
              cases rightPath with
              | mk rightModulePath =>
                  simp only [toModuleId] at equality
                  cases equality
                  rfl

end SourceId

/-- One validated source file under its structured identity. -/
structure WorkspaceFile where
  id : SourceId
  content : String
  deriving Repr, BEq, DecidableEq

namespace WorkspaceFile

/-- Canonical file comparison by structured source identity only. -/
def compareById (left right : WorkspaceFile) : Ordering :=
  SourceId.compare left.id right.id

/-- Non-strict canonical file comparison by structured source identity only. -/
def leById (left right : WorkspaceFile) : Bool :=
  (compareById left right).isLE

@[simp] theorem compareById_eq_iff_id_eq {left right : WorkspaceFile} :
    compareById left right = .eq ↔ left.id = right.id := by
  exact SourceId.compare_eq_iff_eq

theorem leById_refl (file : WorkspaceFile) :
    leById file file = true := by
  exact SourceId.le_refl file.id

theorem leById_trans {a b c : WorkspaceFile}
    (hab : leById a b = true) (hbc : leById b c = true) :
    leById a c = true := by
  exact SourceId.le_trans hab hbc

theorem leById_total (left right : WorkspaceFile) :
    leById left right = true ∨ leById right left = true := by
  exact SourceId.le_total left.id right.id

theorem leById_antisymm {left right : WorkspaceFile}
    (forward : leById left right = true)
    (backward : leById right left = true) :
    left.id = right.id := by
  exact SourceId.le_antisymm forward backward

/-- Canonical file order compares structured source identities only. -/
def before (left right : WorkspaceFile) : Prop :=
  compareById left right = .lt

/-- The UTF-8 content bytes charged to this validated source. -/
def sourceBytes (file : WorkspaceFile) : Nat :=
  file.content.utf8ByteSize

end WorkspaceFile

/-- Canonical external-library order used by validated workspaces. -/
def externalLibraryBefore (left right : ExternalLibraryName) : Prop :=
  ExternalLibraryName.compare left right = .lt

/-- A validated caller workspace in canonical logical order. -/
structure ValidatedUserWorkspace where
  entry : SourceId
  declaredExternalLibraries : List ExternalLibraryName
  files : List WorkspaceFile
  declaredExternalLibrariesSorted :
    declaredExternalLibraries.Pairwise externalLibraryBefore
  declaredExternalLibrariesUnique : declaredExternalLibraries.Nodup
  filesSorted : files.Pairwise WorkspaceFile.before
  fileIdsUnique : (files.map WorkspaceFile.id).Nodup
  entryIsMain : entry.library = .main
  entryPresent : ∃ file ∈ files, file.id = entry
  noStandardFile : ∀ file ∈ files, file.id.library ≠ .standard
  externalFilesDeclared :
    ∀ file ∈ files, ∀ name,
      file.id.library = .external name → name ∈ declaredExternalLibraries
  deriving Repr, DecidableEq

namespace ValidatedUserWorkspace

/-- The number of validated caller-supplied sources. -/
def sourceFiles (workspace : ValidatedUserWorkspace) : Nat :=
  workspace.files.length

/-- The UTF-8 content bytes in validated caller-supplied sources. -/
def sourceBytes (workspace : ValidatedUserWorkspace) : Nat :=
  (workspace.files.map WorkspaceFile.sourceBytes).sum

/-- Finds a validated source by its structured identity. -/
def lookupSource (workspace : ValidatedUserWorkspace) (id : SourceId) : Option WorkspaceFile :=
  workspace.files.find? fun file => decide (file.id = id)

end ValidatedUserWorkspace

end Solcore.Workspace
