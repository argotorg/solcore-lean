import Solcore.Workspace.Syntax
import Solcore.Workspace.Error

set_option autoImplicit false

namespace Solcore.Workspace

namespace Validation

/-- Raw external-library spellings, retaining declaration multiplicity. -/
def rawExternalLibraryNames (raw : RawWorkspace) : List String :=
  raw.externalLibraries.map RawExternalLibrary.name

/-- Successfully parsed external-library names in raw declaration order. -/
def parsedExternalLibraryNames (raw : RawWorkspace) : List ExternalLibraryName :=
  (rawExternalLibraryNames raw).filterMap ExternalLibraryName.parse

/-- One successfully parsed main source, retaining its exact content. -/
def parseMainFile (file : RawSourceFile) : Option WorkspaceFile :=
  (CanonicalSourcePath.parse file.path).map fun path => {
    id := { library := .main, path }
    content := file.content
  }

/-- Successfully parsed main sources in raw occurrence order. -/
def parsedMainFiles (raw : RawWorkspace) : List WorkspaceFile :=
  raw.mainSources.filterMap parseMainFile

/-- One successfully parsed external source before conversion to a workspace file. -/
structure ParsedExternalFile where
  libraryName : ExternalLibraryName
  path : CanonicalSourcePath
  content : String
  deriving Repr, BEq, DecidableEq

namespace ParsedExternalFile

/-- The duplicate-detection key fixed by external library and source path. -/
def key (file : ParsedExternalFile) : ExternalLibraryName × CanonicalSourcePath :=
  (file.libraryName, file.path)

/-- Convert a parsed external occurrence to its structured workspace identity. -/
def toWorkspaceFile (file : ParsedExternalFile) : WorkspaceFile := {
  id := { library := .external file.libraryName, path := file.path }
  content := file.content
}

@[simp] theorem toWorkspaceFile_id (file : ParsedExternalFile) :
    file.toWorkspaceFile.id = {
      library := .external file.libraryName
      path := file.path
    } := rfl

end ParsedExternalFile

/-- Parse the sources of one external declaration when its name is canonical. -/
def parseExternalLibraryFiles
    (library : RawExternalLibrary) : List ParsedExternalFile :=
  match ExternalLibraryName.parse library.name with
  | none => []
  | some libraryName =>
      library.sources.filterMap fun source =>
        (CanonicalSourcePath.parse source.path).map fun path => {
          libraryName
          path
          content := source.content
        }

/-- Successfully parsed external sources, flattened in raw occurrence order. -/
def parsedExternalFiles (raw : RawWorkspace) : List ParsedExternalFile :=
  raw.externalLibraries.flatMap parseExternalLibraryFiles

/-- Parsed external duplicate keys, retaining every source occurrence. -/
def parsedExternalFileKeys
    (raw : RawWorkspace) : List (ExternalLibraryName × CanonicalSourcePath) :=
  (parsedExternalFiles raw).map ParsedExternalFile.key

/-- Emit one marker for each occurrence that has an equal later occurrence. -/
def duplicateErrors {α : Type} [DecidableEq α]
    (makeError : α -> ValidationError) : List α -> List ValidationError
  | [] => []
  | value :: rest =>
      (if value ∈ rest then [makeError value] else []) ++
        duplicateErrors makeError rest

theorem duplicateErrors_eq_nil_iff_nodup {α : Type} [DecidableEq α]
    (makeError : α -> ValidationError) (values : List α) :
    duplicateErrors makeError values = [] ↔ values.Nodup := by
  induction values with
  | nil => simp [duplicateErrors]
  | cons value rest inductionHypothesis =>
      simp [duplicateErrors, inductionHypothesis, List.nodup_cons]

/-- The entry-path error bucket. -/
def invalidEntryPathErrors (raw : RawWorkspace) : List ValidationError :=
  match CanonicalSourcePath.parse raw.entry with
  | none => [.invalidEntryPath raw.entry]
  | some _ => []

/-- Invalid external-name errors, retaining raw occurrence multiplicity. -/
def invalidExternalLibraryNameErrors
    (raw : RawWorkspace) : List ValidationError :=
  raw.externalLibraries.filterMap fun library =>
    match ExternalLibraryName.parse library.name with
    | none => some (.invalidExternalLibraryName library.name)
    | some _ => none

/-- Duplicate raw external-name errors, including invalid spellings. -/
def duplicateExternalLibraryNameErrors
    (raw : RawWorkspace) : List ValidationError :=
  duplicateErrors ValidationError.duplicateExternalLibraryName
    (rawExternalLibraryNames raw)

/-- Invalid main-source-path errors, retaining raw occurrence multiplicity. -/
def invalidMainSourcePathErrors (raw : RawWorkspace) : List ValidationError :=
  raw.mainSources.filterMap fun file =>
    match CanonicalSourcePath.parse file.path with
    | none => some (.invalidMainSourcePath file.path)
    | some _ => none

/-- Invalid external-source-path errors, independent of name validity. -/
def invalidExternalSourcePathErrors
    (raw : RawWorkspace) : List ValidationError :=
  raw.externalLibraries.flatMap fun library =>
    library.sources.filterMap fun file =>
      match CanonicalSourcePath.parse file.path with
      | none => some (.invalidExternalSourcePath library.name file.path)
      | some _ => none

/-- Parsed main source identities, retaining every valid occurrence. -/
def parsedMainFileIds (raw : RawWorkspace) : List SourceId :=
  (parsedMainFiles raw).map WorkspaceFile.id

private def duplicateMainError (id : SourceId) : ValidationError :=
  .duplicateMainSourcePath id.path

/-- Duplicate canonical main-source-path errors. -/
def duplicateMainSourcePathErrors
    (raw : RawWorkspace) : List ValidationError :=
  duplicateErrors duplicateMainError (parsedMainFileIds raw)

private def duplicateExternalError
    (key : ExternalLibraryName × CanonicalSourcePath) : ValidationError :=
  .duplicateExternalSourcePath key.1 key.2

/-- Duplicate external source errors across all same-name declarations. -/
def duplicateExternalSourcePathErrors
    (raw : RawWorkspace) : List ValidationError :=
  duplicateErrors duplicateExternalError (parsedExternalFileKeys raw)

/-- The missing-entry error bucket; invalid entry syntax suppresses this bucket. -/
def missingEntryErrors (raw : RawWorkspace) : List ValidationError :=
  match CanonicalSourcePath.parse raw.entry with
  | none => []
  | some path =>
      if (parsedMainFileIds raw).any fun id =>
          SourceId.compare id { library := .main, path } |>.isEq then
        []
      else
        [.missingEntry path]

/-- Every executable error candidate before canonical sorting and deduplication. -/
def errorCandidates (raw : RawWorkspace) : List ValidationError :=
  invalidEntryPathErrors raw ++
  invalidExternalLibraryNameErrors raw ++
  duplicateExternalLibraryNameErrors raw ++
  invalidMainSourcePathErrors raw ++
  invalidExternalSourcePathErrors raw ++
  duplicateMainSourcePathErrors raw ++
  duplicateExternalSourcePathErrors raw ++
  missingEntryErrors raw

@[simp] theorem errorCandidates_eq_nil_iff (raw : RawWorkspace) :
    errorCandidates raw = [] ↔
      invalidEntryPathErrors raw = [] ∧
      invalidExternalLibraryNameErrors raw = [] ∧
      duplicateExternalLibraryNameErrors raw = [] ∧
      invalidMainSourcePathErrors raw = [] ∧
      invalidExternalSourcePathErrors raw = [] ∧
      duplicateMainSourcePathErrors raw = [] ∧
      duplicateExternalSourcePathErrors raw = [] ∧
      missingEntryErrors raw = [] := by
  simp [errorCandidates]

/-- Sort and deduplicate structural errors in the order fixed by ADR-0014. -/
def canonicalizeErrors (errors : List ValidationError) : List ValidationError :=
  errors.eraseDups.mergeSort ValidationError.le

@[simp] theorem mem_canonicalizeErrors
    {error : ValidationError} {errors : List ValidationError} :
    error ∈ canonicalizeErrors errors ↔ error ∈ errors := by
  simp [canonicalizeErrors]

private theorem eraseDups_nodup
    (errors : List ValidationError) : errors.eraseDups.Nodup := by
  cases errors with
  | nil => simp
  | cons error rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups, List.mem_filter] at member
        simp at member
      · exact eraseDups_nodup (rest.filter fun other => !other == error)
termination_by errors.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Canonicalized errors are duplicate-free. -/
theorem canonicalizeErrors_nodup (errors : List ValidationError) :
    (canonicalizeErrors errors).Nodup := by
  unfold canonicalizeErrors
  exact (List.mergeSort_perm errors.eraseDups ValidationError.le).nodup_iff.mpr
    (eraseDups_nodup errors)

/-- Canonicalized errors are sorted by their closed diagnostic order. -/
theorem canonicalizeErrors_sorted (errors : List ValidationError) :
    (canonicalizeErrors errors).Pairwise
      (fun left right => ValidationError.le left right) := by
  unfold canonicalizeErrors
  apply List.pairwise_mergeSort
  · intro first second third firstSecond secondThird
    exact ValidationError.le_trans first second third firstSecond secondThird
  · intro left right
    exact ValidationError.le_total left right

theorem canonicalizeErrors_eq_nil_iff (errors : List ValidationError) :
    canonicalizeErrors errors = [] ↔ errors = [] := by
  constructor
  · intro canonicalNil
    rw [List.eq_nil_iff_forall_not_mem]
    intro error member
    have canonicalMember : error ∈ canonicalizeErrors errors :=
      mem_canonicalizeErrors.mpr member
    simp [canonicalNil] at canonicalMember
  · intro errorsNil
    simp [canonicalizeErrors, errorsNil]

/-- The complete canonical executable diagnostic list. -/
def validationErrors (raw : RawWorkspace) : List ValidationError :=
  canonicalizeErrors (errorCandidates raw)

@[simp] theorem validationErrors_eq_nil_iff (raw : RawWorkspace) :
    validationErrors raw = [] ↔ errorCandidates raw = [] :=
  canonicalizeErrors_eq_nil_iff (errorCandidates raw)

@[simp] theorem mem_validationErrors
    {raw : RawWorkspace} {error : ValidationError} :
    error ∈ validationErrors raw ↔ error ∈ errorCandidates raw := by
  simp [validationErrors]

theorem validationErrors_nodup (raw : RawWorkspace) :
    (validationErrors raw).Nodup :=
  canonicalizeErrors_nodup (errorCandidates raw)

theorem validationErrors_sorted (raw : RawWorkspace) :
    (validationErrors raw).Pairwise
      (fun left right => ValidationError.le left right) :=
  canonicalizeErrors_sorted (errorCandidates raw)

/-- Canonical external declarations, sorted by their parsed names. -/
def canonicalExternalLibraryNames
    (raw : RawWorkspace) : List ExternalLibraryName :=
  (parsedExternalLibraryNames raw).mergeSort ExternalLibraryName.le

/-- Successfully parsed files before canonical identity sorting. -/
def parsedWorkspaceFiles (raw : RawWorkspace) : List WorkspaceFile :=
  parsedMainFiles raw ++
    (parsedExternalFiles raw).map ParsedExternalFile.toWorkspaceFile

/-- Canonical caller files, sorted only by structured source identity. -/
def canonicalWorkspaceFiles (raw : RawWorkspace) : List WorkspaceFile :=
  (parsedWorkspaceFiles raw).mergeSort WorkspaceFile.leById

private theorem filterMap_nodup_of_functional
    {α β : Type} {values : List α} {parse : α -> Option β}
    (valuesUnique : values.Nodup)
    (functional : ∀ {left right output},
      parse left = some output -> parse right = some output -> left = right) :
    (values.filterMap parse).Nodup := by
  apply valuesUnique.filterMap parse
  intro left right different output leftParsed otherOutput rightParsed equal
  subst otherOutput
  exact different (functional leftParsed rightParsed)

/-- Facts extracted from the empty executable candidate stream. -/
structure SuccessEvidence (raw : RawWorkspace) where
  entryPath : CanonicalSourcePath
  entryParsed : CanonicalSourcePath.parse raw.entry = some entryPath
  externalNamesUnique : (parsedExternalLibraryNames raw).Nodup
  mainFileIdsUnique : (parsedMainFileIds raw).Nodup
  externalFileKeysUnique : (parsedExternalFileKeys raw).Nodup
  entryPresent :
    ({ library := .main, path := entryPath } : SourceId) ∈
      parsedMainFileIds raw

private def successEvidence
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    SuccessEvidence raw := by
  have buckets := (errorCandidates_eq_nil_iff raw).mp candidatesNil
  have rawExternalNamesUnique : (rawExternalLibraryNames raw).Nodup := by
    apply (duplicateErrors_eq_nil_iff_nodup
      ValidationError.duplicateExternalLibraryName
      (rawExternalLibraryNames raw)).mp
    simpa [duplicateExternalLibraryNameErrors] using buckets.2.2.1
  have externalNamesUnique : (parsedExternalLibraryNames raw).Nodup := by
    unfold parsedExternalLibraryNames
    apply filterMap_nodup_of_functional rawExternalNamesUnique
    intro left right name leftParsed rightParsed
    exact (ExternalLibraryName.text_eq_render_of_parse_eq_some leftParsed).trans
      (ExternalLibraryName.text_eq_render_of_parse_eq_some rightParsed).symm
  have mainFileIdsUnique : (parsedMainFileIds raw).Nodup := by
    apply (duplicateErrors_eq_nil_iff_nodup duplicateMainError
      (parsedMainFileIds raw)).mp
    simpa [duplicateMainSourcePathErrors] using buckets.2.2.2.2.2.1
  have externalFileKeysUnique : (parsedExternalFileKeys raw).Nodup := by
    apply (duplicateErrors_eq_nil_iff_nodup duplicateExternalError
      (parsedExternalFileKeys raw)).mp
    simpa [duplicateExternalSourcePathErrors] using
      buckets.2.2.2.2.2.2.1
  cases entryResult : CanonicalSourcePath.parse raw.entry with
  | none =>
      simp [invalidEntryPathErrors, entryResult] at buckets
  | some entryPath =>
      have entryPresent :
          ({ library := .main, path := entryPath } : SourceId) ∈
            parsedMainFileIds raw := by
        have missingNil := buckets.2.2.2.2.2.2.2
        have anyTrue :
            (parsedMainFileIds raw).any (fun id =>
              SourceId.compare id {
                library := .main
                path := entryPath
              } |>.isEq) = true := by
          cases anyResult :
              (parsedMainFileIds raw).any (fun id =>
                SourceId.compare id {
                  library := .main
                  path := entryPath
                } |>.isEq) with
          | false =>
              simp [missingEntryErrors, entryResult, anyResult] at missingNil
          | true => rfl
        obtain ⟨id, member, equalComparison⟩ :=
          List.any_eq_true.mp anyTrue
        have idEqual : id = ({
            library := .main
            path := entryPath
          } : SourceId) := by
          apply SourceId.compare_eq_iff_eq.mp
          exact Ordering.isEq_iff_eq_eq.mp equalComparison
        simpa [idEqual] using member
      exact {
        entryPath
        entryParsed := entryResult
        externalNamesUnique
        mainFileIdsUnique
        externalFileKeysUnique
        entryPresent
      }

private theorem pairwise_lt_of_le_of_key_nodup
    {α β : Type} (key : α -> β) (cmp : α -> α -> Ordering)
    (compareEqual : ∀ {left right}, cmp left right = .eq ->
      key left = key right)
    {values : List α}
    (sorted : values.Pairwise fun left right =>
      (cmp left right).isLE = true)
    (keysUnique : (values.map key).Nodup) :
    values.Pairwise fun left right => cmp left right = .lt := by
  induction values with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at sorted ⊢
      rw [List.map_cons, List.nodup_cons] at keysUnique
      constructor
      · intro other member
        have headOther := sorted.1 other member
        cases comparison : cmp head other with
        | lt => rfl
        | eq =>
            have keyEqual := compareEqual comparison
            have keyMember : key other ∈ tail.map key :=
              List.mem_map.mpr ⟨other, member, rfl⟩
            exact (keysUnique.1 (keyEqual ▸ keyMember)).elim
        | gt => simp [comparison] at headOther
      · exact inductionHypothesis sorted.2 keysUnique.2

/-- Executable validation errors are in strict canonical order. -/
theorem validationErrors_strictlySorted (raw : RawWorkspace) :
    (validationErrors raw).Pairwise fun left right =>
      ValidationError.compare left right = .lt := by
  apply pairwise_lt_of_le_of_key_nodup
    (fun error : ValidationError => error)
    ValidationError.compare
  · exact ValidationError.compare_eq_iff_eq.mp
  · exact validationErrors_sorted raw
  · simpa using validationErrors_nodup raw

private theorem canonicalExternalLibraryNames_unique
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    (canonicalExternalLibraryNames raw).Nodup := by
  unfold canonicalExternalLibraryNames
  exact (List.mergeSort_perm (parsedExternalLibraryNames raw)
    ExternalLibraryName.le).nodup_iff.mpr evidence.externalNamesUnique

private theorem canonicalExternalLibraryNames_sorted
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    (canonicalExternalLibraryNames raw).Pairwise externalLibraryBefore := by
  apply pairwise_lt_of_le_of_key_nodup
    (fun name : ExternalLibraryName => name)
    ExternalLibraryName.compare
  · intro left right equal
    exact ExternalLibraryName.compare_eq_iff_eq.mp equal
  · unfold canonicalExternalLibraryNames
    apply List.pairwise_mergeSort
    · intro first second third firstSecond secondThird
      exact ExternalLibraryName.le_trans firstSecond secondThird
    · intro left right
      simpa [ExternalLibraryName.le] using
        ExternalLibraryName.le_total left right
  · simpa using canonicalExternalLibraryNames_unique raw evidence

private theorem parsedMainFile_is_main
    {raw : RawWorkspace} {file : WorkspaceFile}
    (member : file ∈ parsedMainFiles raw) :
    file.id.library = .main := by
  rw [parsedMainFiles, List.mem_filterMap] at member
  obtain ⟨rawFile, _, parsed⟩ := member
  unfold parseMainFile at parsed
  cases pathResult : CanonicalSourcePath.parse rawFile.path with
  | none => simp [pathResult] at parsed
  | some path =>
      simp [pathResult] at parsed
      subst file
      rfl

private theorem parsedExternalFile_is_external
    {file : ParsedExternalFile} :
    file.toWorkspaceFile.id.library = .external file.libraryName := rfl

private theorem parsedExternalFile_library_mem_names
    {raw : RawWorkspace} {file : ParsedExternalFile}
    (member : file ∈ parsedExternalFiles raw) :
    file.libraryName ∈ parsedExternalLibraryNames raw := by
  rw [parsedExternalFiles, List.mem_flatMap] at member
  obtain ⟨library, libraryMember, fileMember⟩ := member
  unfold parseExternalLibraryFiles at fileMember
  cases nameResult : ExternalLibraryName.parse library.name with
  | none => simp [nameResult] at fileMember
  | some libraryName =>
      simp only [nameResult] at fileMember
      have nameEqual : file.libraryName = libraryName := by
        rw [List.mem_filterMap] at fileMember
        obtain ⟨source, _, sourceParsed⟩ := fileMember
        cases pathResult : CanonicalSourcePath.parse source.path with
        | none => simp [pathResult] at sourceParsed
        | some path =>
            simp [pathResult] at sourceParsed
            subst file
            rfl
      subst libraryName
      unfold parsedExternalLibraryNames rawExternalLibraryNames
      rw [List.mem_filterMap]
      exact ⟨library.name,
        List.mem_map.mpr ⟨library, libraryMember, rfl⟩,
        nameResult⟩

private theorem nodup_map_of_nodup_map
    {α β γ : Type} {values : List α} (first : α -> β) (second : α -> γ)
    (unique : (values.map first).Nodup)
    (reflected : ∀ {left right}, second left = second right ->
      first left = first right) :
    (values.map second).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at unique ⊢
  exact unique.imp fun firstDifferent secondEqual =>
    firstDifferent (reflected secondEqual)

private theorem parsedExternalWorkspaceFileIds_unique
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    ((parsedExternalFiles raw).map fun file =>
      file.toWorkspaceFile.id).Nodup := by
  apply nodup_map_of_nodup_map ParsedExternalFile.key
    (fun file => file.toWorkspaceFile.id)
    evidence.externalFileKeysUnique
  intro left right equal
  cases left
  cases right
  simp [ParsedExternalFile.key, ParsedExternalFile.toWorkspaceFile] at equal ⊢
  exact equal

private theorem parsedWorkspaceFileIds_unique
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    ((parsedWorkspaceFiles raw).map WorkspaceFile.id).Nodup := by
  rw [parsedWorkspaceFiles, List.map_append, List.map_map,
    List.nodup_append]
  refine ⟨evidence.mainFileIdsUnique,
    parsedExternalWorkspaceFileIds_unique raw evidence, ?_⟩
  intro mainId mainMember externalId externalMember equal
  rw [List.mem_map] at externalMember
  obtain ⟨externalFile, _, rfl⟩ := externalMember
  have mainLibrary : mainId.library = .main := by
    rw [List.mem_map] at mainMember
    obtain ⟨mainFile, mainFileMember, rfl⟩ := mainMember
    exact parsedMainFile_is_main mainFileMember
  have libraryEqual := congrArg SourceId.library equal
  simp [mainLibrary] at libraryEqual

private theorem canonicalWorkspaceFileIds_unique
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    ((canonicalWorkspaceFiles raw).map WorkspaceFile.id).Nodup := by
  unfold canonicalWorkspaceFiles
  have permutation := (List.mergeSort_perm (parsedWorkspaceFiles raw)
    WorkspaceFile.leById).map WorkspaceFile.id
  exact permutation.nodup_iff.mpr
    (parsedWorkspaceFileIds_unique raw evidence)

private theorem canonicalWorkspaceFiles_sorted
    (raw : RawWorkspace) (evidence : SuccessEvidence raw) :
    (canonicalWorkspaceFiles raw).Pairwise WorkspaceFile.before := by
  apply pairwise_lt_of_le_of_key_nodup WorkspaceFile.id
    WorkspaceFile.compareById
  · exact WorkspaceFile.compareById_eq_iff_id_eq.mp
  · unfold canonicalWorkspaceFiles
    apply List.pairwise_mergeSort
    · intro first second third firstSecond secondThird
      exact WorkspaceFile.leById_trans firstSecond secondThird
    · intro left right
      simpa [WorkspaceFile.leById] using
        WorkspaceFile.leById_total left right
  · exact canonicalWorkspaceFileIds_unique raw evidence

/-- Construct the unique canonical validated value from an empty candidate stream. -/
def buildValidatedWorkspace
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    ValidatedUserWorkspace := by
  let evidence := successEvidence raw candidatesNil
  exact {
    entry := { library := .main, path := evidence.entryPath }
    declaredExternalLibraries := canonicalExternalLibraryNames raw
    files := canonicalWorkspaceFiles raw
    declaredExternalLibrariesSorted :=
      canonicalExternalLibraryNames_sorted raw evidence
    declaredExternalLibrariesUnique :=
      canonicalExternalLibraryNames_unique raw evidence
    filesSorted := canonicalWorkspaceFiles_sorted raw evidence
    fileIdsUnique := canonicalWorkspaceFileIds_unique raw evidence
    entryIsMain := rfl
    entryPresent := by
      have entryMember := evidence.entryPresent
      rw [parsedMainFileIds, List.mem_map] at entryMember
      obtain ⟨file, fileMember, fileId⟩ := entryMember
      exact ⟨file, by
        rw [canonicalWorkspaceFiles, List.mem_mergeSort,
          parsedWorkspaceFiles, List.mem_append]
        exact Or.inl fileMember,
        fileId⟩
    noStandardFile := by
      intro file fileMember
      rw [canonicalWorkspaceFiles, List.mem_mergeSort,
        parsedWorkspaceFiles, List.mem_append] at fileMember
      rcases fileMember with mainMember | externalMember
      · have mainLibrary := parsedMainFile_is_main mainMember
        simp [mainLibrary]
      · rw [List.mem_map] at externalMember
        obtain ⟨externalFile, _, rfl⟩ := externalMember
        simp [ParsedExternalFile.toWorkspaceFile]
    externalFilesDeclared := by
      intro file fileMember name libraryEqual
      rw [canonicalWorkspaceFiles, List.mem_mergeSort,
        parsedWorkspaceFiles, List.mem_append] at fileMember
      rcases fileMember with mainMember | externalMember
      · have mainLibrary := parsedMainFile_is_main mainMember
        simp [mainLibrary] at libraryEqual
      · rw [List.mem_map] at externalMember
        obtain ⟨externalFile, externalFileMember, rfl⟩ := externalMember
        have nameEqual : externalFile.libraryName = name := by
          simpa [ParsedExternalFile.toWorkspaceFile] using libraryEqual
        subst name
        rw [canonicalExternalLibraryNames, List.mem_mergeSort]
        exact parsedExternalFile_library_mem_names externalFileMember
  }

@[simp] theorem buildValidatedWorkspace_declaredExternalLibraries
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    (buildValidatedWorkspace raw candidatesNil).declaredExternalLibraries =
      canonicalExternalLibraryNames raw := rfl

@[simp] theorem buildValidatedWorkspace_files
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    (buildValidatedWorkspace raw candidatesNil).files =
      canonicalWorkspaceFiles raw := rfl

theorem buildValidatedWorkspace_entry_parsed
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    CanonicalSourcePath.parse raw.entry =
      some (buildValidatedWorkspace raw candidatesNil).entry.path := by
  exact (successEvidence raw candidatesNil).entryParsed

/--
Validate every structural condition, returning all canonical errors or the
canonical proof-carrying caller workspace.
-/
def validate (raw : RawWorkspace) :
    Except (List ValidationError) ValidatedUserWorkspace :=
  let errors := validationErrors raw
  if errorsNil : errors = [] then
    .ok (buildValidatedWorkspace raw
      ((validationErrors_eq_nil_iff raw).mp errorsNil))
  else
    .error errors

@[simp] theorem validate_eq_error_of_validationErrors_ne_nil
    {raw : RawWorkspace} (errorsNotNil : validationErrors raw ≠ []) :
    validate raw = .error (validationErrors raw) := by
  simp [validate, errorsNotNil]

theorem validate_eq_ok_of_validationErrors_eq_nil
    {raw : RawWorkspace} (errorsNil : validationErrors raw = []) :
    validate raw = .ok (buildValidatedWorkspace raw
      ((validationErrors_eq_nil_iff raw).mp errorsNil)) := by
  simp [validate, errorsNil]

theorem validate_eq_error_iff
    {raw : RawWorkspace} {errors : List ValidationError} :
    validate raw = .error errors ↔
      validationErrors raw = errors ∧ errors ≠ [] := by
  by_cases errorsNil : validationErrors raw = []
  · simp [validate, errorsNil]
  · simp only [validate, errorsNil, ↓reduceDIte, Except.error.injEq]
    constructor
    · intro equality
      exact ⟨equality, fun errorsEmpty =>
        errorsNil (equality.trans errorsEmpty)⟩
    · exact fun conjunction => conjunction.1

end Validation

export Validation (validate validationErrors)

end Solcore.Workspace
