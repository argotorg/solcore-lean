import Solcore.Workspace.Syntax
import Solcore.Workspace.Error

set_option autoImplicit false

namespace Solcore.Workspace

/-- Two distinct positions in a list satisfy the same predicate. -/
def AtLeastTwo {α : Type} (values : List α) (predicate : α -> Prop) : Prop :=
  ∃ leading first middle second trailing,
    values = leading ++ first :: middle ++ second :: trailing ∧
      predicate first ∧ predicate second

namespace RawWorkspace

/-- All source occurrences belonging to one exact raw library spelling. -/
def externalSourcesNamed (workspace : RawWorkspace) (rawName : String) :
    List RawSourceFile :=
  workspace.externalLibraries.flatMap fun library =>
    if library.name = rawName then library.sources else []

/-- External source occurrences tagged with their exact raw library spelling. -/
def taggedExternalSources (workspace : RawWorkspace) :
    List (String × RawSourceFile) :=
  workspace.externalLibraries.flatMap fun library =>
    library.sources.map fun source => (library.name, source)

end RawWorkspace

namespace ValidationError

/-- The declarative applicability relation for every closed validation error. -/
def Applies (workspace : RawWorkspace) : ValidationError -> Prop
  | .invalidEntryPath rawEntry =>
      rawEntry = workspace.entry ∧
        ¬∃ path, CanonicalPathOf rawEntry path
  | .invalidExternalLibraryName rawName =>
      (∃ library ∈ workspace.externalLibraries,
        library.name = rawName) ∧
        ¬∃ name, ExternalLibraryNameOf rawName name
  | .duplicateExternalLibraryName rawName =>
      AtLeastTwo workspace.externalLibraries fun library =>
        library.name = rawName
  | .invalidMainSourcePath rawPath =>
      (∃ source ∈ workspace.mainSources, source.path = rawPath) ∧
        ¬∃ path, CanonicalPathOf rawPath path
  | .invalidExternalSourcePath rawLibraryName rawPath =>
      (∃ library ∈ workspace.externalLibraries,
        library.name = rawLibraryName ∧
          ∃ source ∈ library.sources, source.path = rawPath) ∧
        ¬∃ path, CanonicalPathOf rawPath path
  | .duplicateMainSourcePath path =>
      AtLeastTwo workspace.mainSources fun source =>
        CanonicalPathOf source.path path
  | .duplicateExternalSourcePath libraryName path =>
      ∃ rawName,
        ExternalLibraryNameOf rawName libraryName ∧
          AtLeastTwo (workspace.externalSourcesNamed rawName) fun source =>
            CanonicalPathOf source.path path
  | .missingEntry path =>
      CanonicalPathOf workspace.entry path ∧
        ¬∃ source ∈ workspace.mainSources,
          CanonicalPathOf source.path path

@[simp] theorem applies_invalidEntryPath
    (workspace : RawWorkspace) (rawEntry : String) :
    Applies workspace (.invalidEntryPath rawEntry) ↔
      rawEntry = workspace.entry ∧
        ¬∃ path, CanonicalPathOf rawEntry path :=
  Iff.rfl

@[simp] theorem applies_invalidExternalLibraryName
    (workspace : RawWorkspace) (rawName : String) :
    Applies workspace (.invalidExternalLibraryName rawName) ↔
      (∃ library ∈ workspace.externalLibraries,
        library.name = rawName) ∧
        ¬∃ name, ExternalLibraryNameOf rawName name :=
  Iff.rfl

@[simp] theorem applies_duplicateExternalLibraryName
    (workspace : RawWorkspace) (rawName : String) :
    Applies workspace (.duplicateExternalLibraryName rawName) ↔
      AtLeastTwo workspace.externalLibraries fun library =>
        library.name = rawName :=
  Iff.rfl

@[simp] theorem applies_invalidMainSourcePath
    (workspace : RawWorkspace) (rawPath : String) :
    Applies workspace (.invalidMainSourcePath rawPath) ↔
      (∃ source ∈ workspace.mainSources, source.path = rawPath) ∧
        ¬∃ path, CanonicalPathOf rawPath path :=
  Iff.rfl

@[simp] theorem applies_invalidExternalSourcePath
    (workspace : RawWorkspace) (rawLibraryName rawPath : String) :
    Applies workspace (.invalidExternalSourcePath rawLibraryName rawPath) ↔
      (∃ library ∈ workspace.externalLibraries,
        library.name = rawLibraryName ∧
          ∃ source ∈ library.sources, source.path = rawPath) ∧
        ¬∃ path, CanonicalPathOf rawPath path :=
  Iff.rfl

@[simp] theorem applies_duplicateMainSourcePath
    (workspace : RawWorkspace) (path : CanonicalSourcePath) :
    Applies workspace (.duplicateMainSourcePath path) ↔
      AtLeastTwo workspace.mainSources fun source =>
        CanonicalPathOf source.path path :=
  Iff.rfl

@[simp] theorem applies_duplicateExternalSourcePath
    (workspace : RawWorkspace) (libraryName : ExternalLibraryName)
    (path : CanonicalSourcePath) :
    Applies workspace (.duplicateExternalSourcePath libraryName path) ↔
      ∃ rawName,
        ExternalLibraryNameOf rawName libraryName ∧
          AtLeastTwo (workspace.externalSourcesNamed rawName) fun source =>
            CanonicalPathOf source.path path :=
  Iff.rfl

@[simp] theorem applies_missingEntry
    (workspace : RawWorkspace) (path : CanonicalSourcePath) :
    Applies workspace (.missingEntry path) ↔
      CanonicalPathOf workspace.entry path ∧
        ¬∃ source ∈ workspace.mainSources,
          CanonicalPathOf source.path path :=
  Iff.rfl

/-- Strict canonical order on validation errors. -/
def before (left right : ValidationError) : Prop :=
  ValidationError.compare left right = .lt

end ValidationError

/-- The unique canonical list containing exactly all applicable errors. -/
structure ValidationErrorsFor
    (workspace : RawWorkspace) (errors : List ValidationError) : Prop where
  sorted : errors.Pairwise ValidationError.before
  unique : errors.Nodup
  applies_iff_mem :
    ∀ error, error ∈ errors ↔ ValidationError.Applies workspace error

namespace ValidationErrorsFor

/-- The canonical error list for a raw workspace is unique. -/
theorem functional {workspace : RawWorkspace}
    {first second : List ValidationError}
    (firstFor : ValidationErrorsFor workspace first)
    (secondFor : ValidationErrorsFor workspace second) :
    first = second := by
  have permutation : first.Perm second := by
    apply List.perm_iff_count.mpr
    intro error
    rw [firstFor.unique.count, secondFor.unique.count]
    by_cases applies : ValidationError.Applies workspace error
    · rw [if_pos ((firstFor.applies_iff_mem error).2 applies)]
      rw [if_pos ((secondFor.applies_iff_mem error).2 applies)]
    · rw [if_neg fun member =>
          applies ((firstFor.applies_iff_mem error).1 member)]
      rw [if_neg fun member =>
          applies ((secondFor.applies_iff_mem error).1 member)]
  apply List.Perm.eq_of_pairwise
      (le := ValidationError.before) _
      firstFor.sorted secondFor.sorted permutation
  intro left right _ _ leftRight rightLeft
  have cycle : ValidationError.compare left left = .lt :=
    ValidationError.compare_lt_trans leftRight rightLeft
  simp at cycle

end ValidationErrorsFor

/-- No structural validation error applies to the raw workspace. -/
def NoValidationErrorApplies (workspace : RawWorkspace) : Prop :=
  ∀ error, ¬ValidationError.Applies workspace error

/-- Pointwise correspondence between two lists. -/
inductive ListCorresponds {α β : Type} (relation : α -> β -> Prop) :
    List α -> List β -> Prop where
  | nil : ListCorresponds relation [] []
  | cons {left : α} {right : β} {lefts : List α} {rights : List β} :
      relation left right ->
      ListCorresponds relation lefts rights ->
      ListCorresponds relation (left :: lefts) (right :: rights)

namespace ListCorresponds

/-- Pointwise functional relations induce functional list correspondence. -/
theorem functional {α β : Type} {relation : α -> β -> Prop}
    (relationFunctional :
      ∀ {left : α} {first second : β},
        relation left first -> relation left second -> first = second) :
    ∀ {lefts : List α} {first second : List β},
      ListCorresponds relation lefts first ->
      ListCorresponds relation lefts second ->
      first = second := by
  intro lefts first second firstGraph secondGraph
  induction firstGraph generalizing second with
  | nil =>
      cases secondGraph
      rfl
  | cons headGraph tailGraph inductionHypothesis =>
      cases secondGraph with
      | cons otherHeadGraph otherTailGraph =>
          rw [relationFunctional headGraph otherHeadGraph]
          rw [inductionHypothesis otherTailGraph]

end ListCorresponds

/-- A raw main source mapped to its structured identity without parsing calls. -/
def MainFileOf (raw : RawSourceFile) (file : WorkspaceFile) : Prop :=
  ∃ path,
    CanonicalPathOf raw.path path ∧
      file = {
        id := { library := .main, path }
        content := raw.content
      }

namespace MainFileOf

theorem functional {raw : RawSourceFile} {first second : WorkspaceFile}
    (firstGraph : MainFileOf raw first)
    (secondGraph : MainFileOf raw second) :
    first = second := by
  rcases firstGraph with ⟨firstPath, firstPathGraph, rfl⟩
  rcases secondGraph with ⟨secondPath, secondPathGraph, rfl⟩
  rw [CanonicalPathOf.functional firstPathGraph secondPathGraph]

end MainFileOf

/-- A raw external source mapped under one canonical library name. -/
def ExternalFileOf (libraryName : ExternalLibraryName)
    (raw : RawSourceFile) (file : WorkspaceFile) : Prop :=
  ∃ path,
    CanonicalPathOf raw.path path ∧
      file = {
        id := { library := .external libraryName, path }
        content := raw.content
      }

namespace ExternalFileOf

theorem functional {libraryName : ExternalLibraryName}
    {raw : RawSourceFile} {first second : WorkspaceFile}
    (firstGraph : ExternalFileOf libraryName raw first)
    (secondGraph : ExternalFileOf libraryName raw second) :
    first = second := by
  rcases firstGraph with ⟨firstPath, firstPathGraph, rfl⟩
  rcases secondGraph with ⟨secondPath, secondPathGraph, rfl⟩
  rw [CanonicalPathOf.functional firstPathGraph secondPathGraph]

end ExternalFileOf

/-- Raw-order main file correspondence. -/
def MainFilesOf : List RawSourceFile -> List WorkspaceFile -> Prop :=
  ListCorresponds MainFileOf

namespace MainFilesOf

/-- Raw main sources determine one raw-order structured file list. -/
theorem functional {raw : List RawSourceFile}
    {first second : List WorkspaceFile}
    (firstGraph : MainFilesOf raw first)
    (secondGraph : MainFilesOf raw second) :
    first = second := by
  unfold MainFilesOf at firstGraph secondGraph
  exact @ListCorresponds.functional
    RawSourceFile WorkspaceFile MainFileOf
    (fun {_} {_} {_} firstRelation secondRelation =>
      MainFileOf.functional firstRelation secondRelation)
    raw first second firstGraph secondGraph

end MainFilesOf

/-- A tagged raw external source mapped through both declarative graphs. -/
def TaggedExternalFileOf (raw : String × RawSourceFile)
    (file : WorkspaceFile) : Prop :=
  ∃ libraryName path,
    ExternalLibraryNameOf raw.1 libraryName ∧
      CanonicalPathOf raw.2.path path ∧
      file = {
        id := { library := .external libraryName, path }
        content := raw.2.content
      }

namespace TaggedExternalFileOf

theorem functional {raw : String × RawSourceFile}
    {first second : WorkspaceFile}
    (firstGraph : TaggedExternalFileOf raw first)
    (secondGraph : TaggedExternalFileOf raw second) :
    first = second := by
  rcases firstGraph with
    ⟨firstName, firstPath, firstNameGraph, firstPathGraph, rfl⟩
  rcases secondGraph with
    ⟨secondName, secondPath, secondNameGraph, secondPathGraph, rfl⟩
  rw [ExternalLibraryNameOf.functional firstNameGraph secondNameGraph]
  rw [CanonicalPathOf.functional firstPathGraph secondPathGraph]

end TaggedExternalFileOf

/-- Raw-order external library-name correspondence, including empty libraries. -/
def ExternalLibraryNamesOf :
    List String -> List ExternalLibraryName -> Prop :=
  ListCorresponds ExternalLibraryNameOf

namespace ExternalLibraryNamesOf

/-- Raw name occurrences determine one canonical raw-order name list. -/
theorem functional {raw : List String}
    {first second : List ExternalLibraryName}
    (firstGraph : ExternalLibraryNamesOf raw first)
    (secondGraph : ExternalLibraryNamesOf raw second) :
    first = second := by
  unfold ExternalLibraryNamesOf at firstGraph secondGraph
  exact @ListCorresponds.functional
    String ExternalLibraryName ExternalLibraryNameOf
    (fun {_} {_} {_} firstRelation secondRelation =>
      ExternalLibraryNameOf.functional firstRelation secondRelation)
    raw first second firstGraph secondGraph

end ExternalLibraryNamesOf

/-- Raw-order correspondence for flattened tagged external sources. -/
def TaggedExternalFilesOf :
    List (String × RawSourceFile) -> List WorkspaceFile -> Prop :=
  ListCorresponds TaggedExternalFileOf

namespace TaggedExternalFilesOf

/-- Tagged raw sources determine one structured raw-order file list. -/
theorem functional {raw : List (String × RawSourceFile)}
    {first second : List WorkspaceFile}
    (firstGraph : TaggedExternalFilesOf raw first)
    (secondGraph : TaggedExternalFilesOf raw second) :
    first = second := by
  unfold TaggedExternalFilesOf at firstGraph secondGraph
  exact @ListCorresponds.functional
    (String × RawSourceFile) WorkspaceFile TaggedExternalFileOf
    (fun {_} {_} {_} firstRelation secondRelation =>
      TaggedExternalFileOf.functional firstRelation secondRelation)
    raw first second firstGraph secondGraph

end TaggedExternalFilesOf

namespace Workspace

/-- Raw-order values witnessing declarative workspace decoding. -/
structure RelationalUserWorkspace where
  entryPath : CanonicalSourcePath
  mainFiles : List WorkspaceFile
  externalLibraryNames : List ExternalLibraryName
  externalFiles : List WorkspaceFile
  deriving Repr, DecidableEq

/-- Declarative successful workspace validation, independent of the executor. -/
def Validates
    (raw : RawWorkspace) (workspace : ValidatedUserWorkspace) : Prop :=
  ∃ relational : RelationalUserWorkspace,
    NoValidationErrorApplies raw ∧
      CanonicalPathOf raw.entry relational.entryPath ∧
      workspace.entry = { library := .main, path := relational.entryPath } ∧
      MainFilesOf raw.mainSources relational.mainFiles ∧
      ExternalLibraryNamesOf
        (raw.externalLibraries.map RawExternalLibrary.name)
        relational.externalLibraryNames ∧
      TaggedExternalFilesOf raw.taggedExternalSources
        relational.externalFiles ∧
      workspace.declaredExternalLibraries.Perm
        relational.externalLibraryNames ∧
      workspace.files.Perm
        (relational.mainFiles ++ relational.externalFiles)

namespace Validates

/-- Declarative successful validation determines one validated workspace. -/
theorem functional {raw : RawWorkspace}
    {first second : ValidatedUserWorkspace}
    (firstValidates : Validates raw first)
    (secondValidates : Validates raw second) :
    first = second := by
  rcases firstValidates with
    ⟨firstRelational, _, firstEntryGraph, firstEntry,
      firstMainGraph, firstNamesGraph, firstExternalFilesGraph,
      firstLibraries, firstFiles⟩
  rcases secondValidates with
    ⟨secondRelational, _, secondEntryGraph, secondEntry,
      secondMainGraph, secondNamesGraph, secondExternalFilesGraph,
      secondLibraries, secondFiles⟩
  have entryPathEqual :
      firstRelational.entryPath = secondRelational.entryPath :=
    CanonicalPathOf.functional firstEntryGraph secondEntryGraph
  have mainFilesEqual :
      firstRelational.mainFiles = secondRelational.mainFiles :=
    MainFilesOf.functional firstMainGraph secondMainGraph
  have externalLibraryNamesEqual :
      firstRelational.externalLibraryNames =
        secondRelational.externalLibraryNames :=
    ExternalLibraryNamesOf.functional firstNamesGraph secondNamesGraph
  have externalFilesEqual :
      firstRelational.externalFiles = secondRelational.externalFiles :=
    TaggedExternalFilesOf.functional
      firstExternalFilesGraph secondExternalFilesGraph
  have entriesEqual : first.entry = second.entry := by
    rw [firstEntry, secondEntry, entryPathEqual]
  have libraryPermutation :
      first.declaredExternalLibraries.Perm
        second.declaredExternalLibraries := by
    rw [externalLibraryNamesEqual] at firstLibraries
    exact firstLibraries.trans secondLibraries.symm
  have librariesEqual :
      first.declaredExternalLibraries =
        second.declaredExternalLibraries := by
    apply List.Perm.eq_of_pairwise
        (le := externalLibraryBefore) _
        first.declaredExternalLibrariesSorted
        second.declaredExternalLibrariesSorted
        libraryPermutation
    intro left right _ _ leftRight rightLeft
    have cycle : ExternalLibraryName.compare left left = .lt :=
      Std.TransCmp.lt_trans
        (cmp := ExternalLibraryName.compare) leftRight rightLeft
    have reflexive : ExternalLibraryName.compare left left = .eq :=
      Std.ReflCmp.compare_self
    rw [reflexive] at cycle
    cases cycle
  have filePermutation : first.files.Perm second.files := by
    rw [mainFilesEqual, externalFilesEqual] at firstFiles
    exact firstFiles.trans secondFiles.symm
  have filesEqual : first.files = second.files := by
    apply List.Perm.eq_of_pairwise
        (le := WorkspaceFile.before) _
        first.filesSorted second.filesSorted filePermutation
    intro left right _ _ leftRight rightLeft
    have cycle : SourceId.compare left.id left.id = .lt :=
      Std.TransCmp.lt_trans
        (cmp := SourceId.compare) leftRight rightLeft
    have reflexive : SourceId.compare left.id left.id = .eq :=
      Std.ReflCmp.compare_self
    rw [reflexive] at cycle
    cases cycle
  cases first
  cases second
  simp_all

end Validates

/-- Declarative rejection with the complete nonempty canonical error list. -/
structure Rejects (raw : RawWorkspace) (errors : List ValidationError) : Prop where
  errorsFor : ValidationErrorsFor raw errors
  nonempty : errors ≠ []

namespace Rejects

/-- A raw workspace has at most one canonical rejection list. -/
theorem functional {raw : RawWorkspace} {first second : List ValidationError}
    (firstRejects : Rejects raw first)
    (secondRejects : Rejects raw second) :
    first = second :=
  ValidationErrorsFor.functional
    firstRejects.errorsFor secondRejects.errorsFor

end Rejects

end Workspace

namespace RawWorkspace

/-- Validation-observational equivalence of raw workspace records. -/
structure Equivalent (left right : RawWorkspace) : Prop where
  entry_eq : left.entry = right.entry
  mainSources_perm : left.mainSources.Perm right.mainSources
  externalLibraryNames_perm :
    (left.externalLibraries.map RawExternalLibrary.name).Perm
      (right.externalLibraries.map RawExternalLibrary.name)
  taggedExternalSources_perm :
    left.taggedExternalSources.Perm right.taggedExternalSources

/-- Raw workspace equivalence is reflexive. -/
theorem equivalent_refl (workspace : RawWorkspace) :
    Equivalent workspace workspace where
  entry_eq := rfl
  mainSources_perm := .refl _
  externalLibraryNames_perm := .refl _
  taggedExternalSources_perm := .refl _

/-- Raw workspace equivalence is symmetric. -/
theorem equivalent_symm {left right : RawWorkspace}
    (equivalent : Equivalent left right) :
    Equivalent right left where
  entry_eq := equivalent.entry_eq.symm
  mainSources_perm := equivalent.mainSources_perm.symm
  externalLibraryNames_perm := equivalent.externalLibraryNames_perm.symm
  taggedExternalSources_perm := equivalent.taggedExternalSources_perm.symm

/-- Raw workspace equivalence is transitive. -/
theorem equivalent_trans {first second third : RawWorkspace}
    (firstSecond : Equivalent first second)
    (secondThird : Equivalent second third) :
    Equivalent first third where
  entry_eq := firstSecond.entry_eq.trans secondThird.entry_eq
  mainSources_perm :=
    firstSecond.mainSources_perm.trans secondThird.mainSources_perm
  externalLibraryNames_perm :=
    firstSecond.externalLibraryNames_perm.trans
      secondThird.externalLibraryNames_perm
  taggedExternalSources_perm :=
    firstSecond.taggedExternalSources_perm.trans
      secondThird.taggedExternalSources_perm

end RawWorkspace

end Solcore.Workspace
