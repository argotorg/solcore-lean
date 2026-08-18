import Solcore.Workspace.Judgment
import Solcore.Workspace.Validation

set_option autoImplicit false

namespace Solcore.Workspace

/-- Parser failure is exactly absence from the declarative source-path graph. -/
theorem parseCanonicalPath_eq_none_iff_no_graph (text : String) :
    parseCanonicalPath text = none ↔
      ¬∃ path, CanonicalPathOf text path := by
  constructor
  · intro parsed ⟨path, graph⟩
    rw [parseCanonicalPath_complete graph] at parsed
    cases parsed
  · intro noGraph
    cases parsed : parseCanonicalPath text with
    | none => rfl
    | some path =>
        exact False.elim (noGraph ⟨path, parseCanonicalPath_sound parsed⟩)

namespace CanonicalSourcePath

/-- The concrete path parser fails exactly when the rendering graph is empty. -/
theorem parse_eq_none_iff_no_graph (text : String) :
    parse text = none ↔ ¬∃ path, CanonicalPathOf text path := by
  simpa [parseCanonicalPath] using
    parseCanonicalPath_eq_none_iff_no_graph text

end CanonicalSourcePath

namespace ExternalLibraryName

/-- Parser failure is exactly absence from the declarative library-name graph. -/
theorem parse_eq_none_iff_no_graph (text : String) :
    parse text = none ↔
      ¬∃ name, ExternalLibraryNameOf text name := by
  constructor
  · intro parsed ⟨name, graph⟩
    rw [parse_complete graph] at parsed
    cases parsed
  · intro noGraph
    cases parsed : parse text with
    | none => rfl
    | some name =>
        exact False.elim (noGraph ⟨name, parse_sound parsed⟩)

/-- Successful library-name parsing is exactly the declarative graph. -/
theorem parse_eq_some_iff_graph (text : String)
    (name : ExternalLibraryName) :
    parse text = some name ↔ ExternalLibraryNameOf text name := by
  constructor
  · exact parse_sound
  · exact parse_complete

end ExternalLibraryName

namespace ListCorresponds

/-- Pointwise correspondence preserves list length. -/
theorem length_eq {α β : Type} {relation : α -> β -> Prop}
    {left : List α} {right : List β}
    (graph : ListCorresponds relation left right) :
    left.length = right.length := by
  induction graph with
  | nil => rfl
  | cons _ _ inductionHypothesis =>
      simp [inductionHypothesis]

/-- A permutation of the raw side can be mirrored on the related side. -/
theorem transport_perm {α β : Type} {relation : α -> β -> Prop}
    {left reordered : List α} {right : List β}
    (permutation : left.Perm reordered)
    (graph : ListCorresponds relation left right) :
    ∃ reorderedRight,
      right.Perm reorderedRight ∧
        ListCorresponds relation reordered reorderedRight := by
  induction permutation generalizing right with
  | nil =>
      cases graph
      exact ⟨[], .refl _, .nil⟩
  | cons value permutation inductionHypothesis =>
      cases graph
      rename_i rightHead rightTail headGraph tailGraph
      obtain ⟨reorderedTail, tailPermutation, reorderedGraph⟩ :=
        inductionHypothesis tailGraph
      exact ⟨_, tailPermutation.cons rightHead,
        .cons headGraph reorderedGraph⟩
  | swap first second tail =>
      cases graph
      rename_i firstRight remainingRight firstGraph remainingGraph
      cases remainingGraph
      rename_i secondRight tailRight secondGraph tailGraph
      exact ⟨_, .swap secondRight firstRight tailRight,
        .cons secondGraph (.cons firstGraph tailGraph)⟩
  | trans firstPermutation secondPermutation firstIH secondIH =>
      obtain ⟨middleRight, rightMiddle, middleGraph⟩ :=
        firstIH graph
      obtain ⟨finalRight, middleFinal, finalGraph⟩ :=
        secondIH middleGraph
      exact ⟨finalRight, rightMiddle.trans middleFinal, finalGraph⟩

/-- Functional correspondence maps permutations to permutations. -/
theorem right_perm_of_left_perm {α β : Type} {relation : α -> β -> Prop}
    (relationFunctional :
      ∀ {left : α} {first second : β},
        relation left first -> relation left second -> first = second)
    {firstLeft secondLeft : List α} {firstRight secondRight : List β}
    (leftPermutation : firstLeft.Perm secondLeft)
    (firstGraph : ListCorresponds relation firstLeft firstRight)
    (secondGraph : ListCorresponds relation secondLeft secondRight) :
    firstRight.Perm secondRight := by
  obtain ⟨transported, permutation, transportedGraph⟩ :=
    transport_perm leftPermutation firstGraph
  have equal : transported = secondRight :=
    @functional α β relation relationFunctional
      secondLeft transported secondRight transportedGraph secondGraph
  subst transported
  exact permutation

/-- A total graph follows a `filterMap` executor pointwise. -/
theorem filterMap_of_total {α β : Type} (relation : α -> β -> Prop)
    (parse : α -> Option β) {values : List α}
    (complete : ∀ {input output},
      relation input output -> parse input = some output)
    (total : ∀ input ∈ values, ∃ output, relation input output) :
    ListCorresponds relation values (values.filterMap parse) := by
  induction values with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      obtain ⟨output, graph⟩ := total head (by simp)
      have parsed := complete graph
      simp only [List.filterMap_cons, parsed]
      apply ListCorresponds.cons graph
      apply inductionHypothesis
      intro input member
      exact total input (by simp [member])

/-- Pointwise measure preservation extends to list totals. -/
theorem sum_map_eq {α β : Type} {relation : α -> β -> Prop}
    (leftMeasure : α -> Nat) (rightMeasure : β -> Nat)
    (preserves : ∀ {left right}, relation left right ->
      leftMeasure left = rightMeasure right)
    {left : List α} {right : List β}
    (graph : ListCorresponds relation left right) :
    (left.map leftMeasure).sum = (right.map rightMeasure).sum := by
  induction graph with
  | nil => rfl
  | cons relationH tailGraph inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons]
      rw [preserves relationH, inductionHypothesis]

end ListCorresponds

/-- Two matching occurrences in a cons list use the head or both lie in the tail. -/
theorem atLeastTwo_cons_iff {α : Type} (predicate : α -> Prop)
    (head : α) (tail : List α) :
    AtLeastTwo (head :: tail) predicate ↔
      (predicate head ∧ ∃ value ∈ tail, predicate value) ∨
        AtLeastTwo tail predicate := by
  constructor
  · rintro ⟨leading, first, middle, second, trailing,
      decomposition, firstMatches, secondMatches⟩
    cases leading with
    | nil =>
        simp only [List.nil_append] at decomposition
        injection decomposition with headEqual tailEqual
        left
        constructor
        · exact headEqual ▸ firstMatches
        · refine ⟨second, ?_, secondMatches⟩
          rw [tailEqual]
          simp
    | cons leadingHead leadingTail =>
        simp only [List.cons_append] at decomposition
        injection decomposition with _ tailEqual
        right
        exact ⟨leadingTail, first, middle, second, trailing,
          tailEqual, firstMatches, secondMatches⟩
  · intro alternatives
    rcases alternatives with headPair | tailPair
    · rcases headPair with ⟨headMatches, value, member, valueMatches⟩
      obtain ⟨leading, trailing, tailEqual⟩ := List.append_of_mem member
      exact ⟨[], head, leading, value, trailing,
        by simp [tailEqual], headMatches, valueMatches⟩
    · rcases tailPair with
        ⟨leading, first, middle, second, trailing,
          decomposition, firstMatches, secondMatches⟩
      exact ⟨head :: leading, first, middle, second, trailing,
        by simp [decomposition], firstMatches, secondMatches⟩

/-- Two equal-key occurrences in a cons list either use the head or lie in the tail. -/
theorem atLeastTwo_cons_eq_iff {α : Type} (head value : α) (tail : List α) :
    AtLeastTwo (head :: tail) (fun candidate => candidate = value) ↔
      (head = value ∧ value ∈ tail) ∨
        AtLeastTwo tail (fun candidate => candidate = value) := by
  constructor
  · rintro ⟨leading, first, middle, second, trailing,
      decomposition, firstEqual, secondEqual⟩
    cases leading with
    | nil =>
        simp only [List.nil_append] at decomposition
        injection decomposition with headEqual tailEqual
        left
        constructor
        · exact headEqual.trans firstEqual
        · rw [tailEqual]
          simp [secondEqual]
    | cons leadingHead leadingTail =>
        simp only [List.cons_append] at decomposition
        injection decomposition with _ tailEqual
        right
        refine ⟨leadingTail, first, middle, second, trailing,
          tailEqual, firstEqual, secondEqual⟩
  · intro alternatives
    rcases alternatives with headPair | tailPair
    · rcases headPair with ⟨headEqual, member⟩
      obtain ⟨leading, trailing, tailEqual⟩ := List.append_of_mem member
      refine ⟨[], head, leading, value, trailing, ?_, headEqual, rfl⟩
      simp [tailEqual]
    · rcases tailPair with
        ⟨leading, first, middle, second, trailing,
          decomposition, firstEqual, secondEqual⟩
      exact ⟨head :: leading, first, middle, second, trailing,
        by simp [decomposition], firstEqual, secondEqual⟩

/-- Mapping a list maps the predicate on its two distinguished occurrences. -/
theorem atLeastTwo_map_iff {α β : Type} (transform : α -> β)
    (predicate : β -> Prop) (values : List α) :
    AtLeastTwo (values.map transform) predicate ↔
      AtLeastTwo values (fun value => predicate (transform value)) := by
  induction values with
  | nil => simp [AtLeastTwo]
  | cons head tail inductionHypothesis =>
      have witnesses :
          (∃ value ∈ tail.map transform, predicate value) ↔
            ∃ value ∈ tail, predicate (transform value) := by
        constructor
        · rintro ⟨value, member, holds⟩
          rw [List.mem_map] at member
          obtain ⟨original, originalMember, rfl⟩ := member
          exact ⟨original, originalMember, holds⟩
        · rintro ⟨value, member, holds⟩
          exact ⟨transform value,
            List.mem_map.mpr ⟨value, member, rfl⟩, holds⟩
      rw [List.map_cons, atLeastTwo_cons_iff,
        atLeastTwo_cons_iff, witnesses, inductionHypothesis]

/-- Filtering successful parses preserves the two-occurrence interpretation. -/
theorem atLeastTwo_filterMap_iff {α β : Type}
    (parse : α -> Option β) (predicate : β -> Prop) (values : List α) :
    AtLeastTwo (values.filterMap parse) predicate ↔
      AtLeastTwo values (fun value =>
        ∃ output, parse value = some output ∧ predicate output) := by
  induction values with
  | nil => simp [AtLeastTwo]
  | cons head tail inductionHypothesis =>
      have witnesses :
          (∃ output ∈ tail.filterMap parse, predicate output) ↔
            ∃ value ∈ tail,
              ∃ output, parse value = some output ∧ predicate output := by
        constructor
        · rintro ⟨output, member, holds⟩
          rw [List.mem_filterMap] at member
          obtain ⟨value, valueMember, parsedValue⟩ := member
          exact ⟨value, valueMember, output, parsedValue, holds⟩
        · rintro ⟨value, valueMember, output, parsedValue, holds⟩
          exact ⟨output,
            List.mem_filterMap.mpr ⟨value, valueMember, parsedValue⟩,
            holds⟩
      cases parsed : parse head with
      | none =>
          simpa [parsed, atLeastTwo_cons_iff] using inductionHypothesis
      | some output =>
          simp only [parsed, List.filterMap_cons, atLeastTwo_cons_iff,
            Option.some.injEq]
          rw [witnesses, inductionHypothesis]
          simp

/-- Pointwise equivalent predicates define the same two-occurrence property. -/
theorem atLeastTwo_congr {α : Type} {values : List α}
    {first second : α -> Prop}
    (equivalent : ∀ value, first value ↔ second value) :
    AtLeastTwo values first ↔ AtLeastTwo values second := by
  constructor
  · rintro ⟨leading, left, middle, right, trailing,
      decomposition, leftHolds, rightHolds⟩
    exact ⟨leading, left, middle, right, trailing, decomposition,
      (equivalent left).mp leftHolds, (equivalent right).mp rightHolds⟩
  · rintro ⟨leading, left, middle, right, trailing,
      decomposition, leftHolds, rightHolds⟩
    exact ⟨leading, left, middle, right, trailing, decomposition,
      (equivalent left).mpr leftHolds, (equivalent right).mpr rightHolds⟩

/-- Permuting occurrences does not change whether two satisfy a predicate. -/
theorem atLeastTwo_perm_iff {α : Type} {first second : List α}
    (permutation : first.Perm second) (predicate : α -> Prop) :
    AtLeastTwo first predicate ↔ AtLeastTwo second predicate := by
  induction permutation with
  | nil => rfl
  | cons head permutation inductionHypothesis =>
      rename_i firstTail secondTail
      have witnessIff :
          (∃ value ∈ firstTail, predicate value) ↔
            ∃ value ∈ secondTail, predicate value := by
        constructor
        · rintro ⟨value, member, holds⟩
          exact ⟨value, permutation.mem_iff.mp member, holds⟩
        · rintro ⟨value, member, holds⟩
          exact ⟨value, permutation.mem_iff.mpr member, holds⟩
      rw [atLeastTwo_cons_iff, atLeastTwo_cons_iff,
        witnessIff, inductionHypothesis]
  | swap first second tail =>
      simp only [atLeastTwo_cons_iff, List.mem_cons]
      constructor
      · intro alternatives
        rcases alternatives with headPair | tailAlternatives
        · rcases headPair with ⟨secondHolds, value, firstOrTail, valueHolds⟩
          rcases firstOrTail with valueEqual | tailMember
          · subst value
            exact Or.inl ⟨valueHolds, second,
              Or.inl rfl, secondHolds⟩
          · exact Or.inr (Or.inl ⟨secondHolds, value,
              tailMember, valueHolds⟩)
        · rcases tailAlternatives with firstPair | tailPair
          · rcases firstPair with ⟨firstHolds, value, member, valueHolds⟩
            exact Or.inl ⟨firstHolds, value,
              Or.inr member, valueHolds⟩
          · exact Or.inr (Or.inr tailPair)
      · intro alternatives
        rcases alternatives with headPair | tailAlternatives
        · rcases headPair with ⟨firstHolds, value, secondOrTail, valueHolds⟩
          rcases secondOrTail with valueEqual | tailMember
          · subst value
            exact Or.inl ⟨valueHolds, first,
              Or.inl rfl, firstHolds⟩
          · exact Or.inr (Or.inl ⟨firstHolds, value,
              tailMember, valueHolds⟩)
        · rcases tailAlternatives with secondPair | tailPair
          · rcases secondPair with ⟨secondHolds, value, member, valueHolds⟩
            exact Or.inl ⟨secondHolds, value,
              Or.inr member, valueHolds⟩
          · exact Or.inr (Or.inr tailPair)
  | trans _ _ firstIH secondIH =>
      exact firstIH.trans secondIH

/-- Permuting a list preserves existential occurrence predicates. -/
theorem exists_mem_perm_iff {α : Type} {first second : List α}
    (permutation : first.Perm second) (predicate : α -> Prop) :
    (∃ value ∈ first, predicate value) ↔
      ∃ value ∈ second, predicate value := by
  constructor
  · rintro ⟨value, member, holds⟩
    exact ⟨value, permutation.mem_iff.mp member, holds⟩
  · rintro ⟨value, member, holds⟩
    exact ⟨value, permutation.mem_iff.mpr member, holds⟩

namespace Validation

/-- Duplicate-marker membership is the declarative two-occurrence condition. -/
theorem mem_duplicateErrors_iff {α : Type} [DecidableEq α]
    (makeError : α -> ValidationError) (values : List α)
    (error : ValidationError) :
    error ∈ duplicateErrors makeError values ↔
      ∃ value,
        makeError value = error ∧
          AtLeastTwo values (fun candidate => candidate = value) := by
  induction values with
  | nil => simp [duplicateErrors, AtLeastTwo]
  | cons head tail inductionHypothesis =>
      by_cases member : head ∈ tail
      · simp only [duplicateErrors, if_pos member, List.singleton_append,
          List.mem_cons]
        rw [inductionHypothesis]
        simp only [atLeastTwo_cons_eq_iff]
        constructor
        · intro alternative
          rcases alternative with headError | tailError
          · exact ⟨head, headError.symm, Or.inl ⟨rfl, member⟩⟩
          · rcases tailError with ⟨value, errorEqual, repeated⟩
            exact ⟨value, errorEqual, Or.inr repeated⟩
        · rintro ⟨value, errorEqual, repeated⟩
          rcases repeated with headRepeated | tailRepeated
          · rcases headRepeated with ⟨headEqual, _⟩
            subst value
            exact Or.inl errorEqual.symm
          · exact Or.inr ⟨value, errorEqual, tailRepeated⟩
      · simp only [duplicateErrors, if_neg member, List.nil_append]
        rw [inductionHypothesis]
        simp only [atLeastTwo_cons_eq_iff]
        constructor
        · rintro ⟨value, errorEqual, repeated⟩
          exact ⟨value, errorEqual, Or.inr repeated⟩
        · rintro ⟨value, errorEqual, repeated⟩
          rcases repeated with headRepeated | tailRepeated
          · rcases headRepeated with ⟨headEqual, valueMember⟩
            subst value
            exact False.elim (member valueMember)
          · exact ⟨value, errorEqual, tailRepeated⟩

/-- When the emitted key is injective on the input, duplicate markers count it directly. -/
theorem mem_duplicateErrors_iff_applied {α : Type} [DecidableEq α]
    (makeError : α -> ValidationError) (values : List α)
    (reflects : ∀ {left right},
      left ∈ values -> right ∈ values ->
        makeError left = makeError right -> left = right)
    (error : ValidationError) :
    error ∈ duplicateErrors makeError values ↔
      AtLeastTwo values (fun value => makeError value = error) := by
  rw [mem_duplicateErrors_iff]
  constructor
  · rintro ⟨value, valueError, leading, first, middle, second, trailing,
      decomposition, firstEqual, secondEqual⟩
    exact ⟨leading, first, middle, second, trailing, decomposition,
      firstEqual ▸ valueError, secondEqual ▸ valueError⟩
  · rintro ⟨leading, first, middle, second, trailing,
      decomposition, firstError, secondError⟩
    have firstMember : first ∈ values := by
      rw [decomposition]
      simp
    have secondMember : second ∈ values := by
      rw [decomposition]
      simp
    have equal : first = second :=
      reflects firstMember secondMember (firstError.trans secondError.symm)
    exact ⟨first, firstError,
      leading, first, middle, second, trailing,
      decomposition, rfl, equal.symm⟩

theorem mem_invalidEntryPathErrors_iff
    (raw : RawWorkspace) (rawEntry : String) :
    .invalidEntryPath rawEntry ∈ invalidEntryPathErrors raw ↔
      ValidationError.Applies raw (.invalidEntryPath rawEntry) := by
  rw [ValidationError.applies_invalidEntryPath]
  cases parsed : CanonicalSourcePath.parse raw.entry with
  | none =>
      have noGraph :=
        (CanonicalSourcePath.parse_eq_none_iff_no_graph raw.entry).mp parsed
      constructor
      · intro member
        simp [invalidEntryPathErrors, parsed] at member
        subst rawEntry
        exact ⟨rfl, noGraph⟩
      · rintro ⟨entryEqual, _⟩
        subst rawEntry
        simp [invalidEntryPathErrors, parsed]
  | some path =>
      have graph : CanonicalPathOf raw.entry path := by
        apply parseCanonicalPath_sound
        simpa [parseCanonicalPath] using parsed
      constructor
      · intro member
        simp [invalidEntryPathErrors, parsed] at member
      · rintro ⟨entryEqual, noGraph⟩
        subst rawEntry
        exact False.elim (noGraph ⟨path, graph⟩)

theorem mem_invalidExternalLibraryNameErrors_iff
    (raw : RawWorkspace) (rawName : String) :
    .invalidExternalLibraryName rawName ∈
        invalidExternalLibraryNameErrors raw ↔
      ValidationError.Applies raw
        (.invalidExternalLibraryName rawName) := by
  rw [ValidationError.applies_invalidExternalLibraryName]
  constructor
  · intro member
    rw [invalidExternalLibraryNameErrors, List.mem_filterMap] at member
    obtain ⟨library, libraryMember, emitted⟩ := member
    cases parsed : ExternalLibraryName.parse library.name with
    | none =>
        simp [parsed] at emitted
        subst rawName
        exact ⟨⟨library, libraryMember, rfl⟩,
          (ExternalLibraryName.parse_eq_none_iff_no_graph library.name).mp parsed⟩
    | some name => simp [parsed] at emitted
  · rintro ⟨⟨library, libraryMember, nameEqual⟩, noGraph⟩
    subst rawName
    have parsed : ExternalLibraryName.parse library.name = none :=
      (ExternalLibraryName.parse_eq_none_iff_no_graph library.name).mpr noGraph
    rw [invalidExternalLibraryNameErrors, List.mem_filterMap]
    exact ⟨library, libraryMember, by simp [parsed]⟩

theorem mem_duplicateExternalLibraryNameErrors_iff
    (raw : RawWorkspace) (rawName : String) :
    .duplicateExternalLibraryName rawName ∈
        duplicateExternalLibraryNameErrors raw ↔
      ValidationError.Applies raw
        (.duplicateExternalLibraryName rawName) := by
  rw [ValidationError.applies_duplicateExternalLibraryName]
  unfold duplicateExternalLibraryNameErrors
  rw [mem_duplicateErrors_iff_applied]
  · unfold rawExternalLibraryNames
    rw [atLeastTwo_map_iff]
    simp
  · intro left right _ _ equal
    simpa using equal

theorem mem_invalidMainSourcePathErrors_iff
    (raw : RawWorkspace) (rawPath : String) :
    .invalidMainSourcePath rawPath ∈ invalidMainSourcePathErrors raw ↔
      ValidationError.Applies raw (.invalidMainSourcePath rawPath) := by
  rw [ValidationError.applies_invalidMainSourcePath]
  constructor
  · intro member
    rw [invalidMainSourcePathErrors, List.mem_filterMap] at member
    obtain ⟨source, sourceMember, emitted⟩ := member
    cases parsed : CanonicalSourcePath.parse source.path with
    | none =>
        simp [parsed] at emitted
        subst rawPath
        exact ⟨⟨source, sourceMember, rfl⟩,
          (CanonicalSourcePath.parse_eq_none_iff_no_graph source.path).mp parsed⟩
    | some path => simp [parsed] at emitted
  · rintro ⟨⟨source, sourceMember, pathEqual⟩, noGraph⟩
    subst rawPath
    have parsed : CanonicalSourcePath.parse source.path = none :=
      (CanonicalSourcePath.parse_eq_none_iff_no_graph source.path).mpr noGraph
    rw [invalidMainSourcePathErrors, List.mem_filterMap]
    exact ⟨source, sourceMember, by simp [parsed]⟩

theorem mem_invalidExternalSourcePathErrors_iff
    (raw : RawWorkspace) (rawName rawPath : String) :
    .invalidExternalSourcePath rawName rawPath ∈
        invalidExternalSourcePathErrors raw ↔
      ValidationError.Applies raw
        (.invalidExternalSourcePath rawName rawPath) := by
  rw [ValidationError.applies_invalidExternalSourcePath]
  constructor
  · intro member
    rw [invalidExternalSourcePathErrors, List.mem_flatMap] at member
    obtain ⟨library, libraryMember, sourceMember⟩ := member
    rw [List.mem_filterMap] at sourceMember
    obtain ⟨source, rawSourceMember, emitted⟩ := sourceMember
    cases parsed : CanonicalSourcePath.parse source.path with
    | none =>
        simp [parsed] at emitted
        rcases emitted with ⟨nameEqual, pathEqual⟩
        subst rawName
        subst rawPath
        exact ⟨⟨library, libraryMember, rfl,
          source, rawSourceMember, rfl⟩,
          (CanonicalSourcePath.parse_eq_none_iff_no_graph source.path).mp parsed⟩
    | some path => simp [parsed] at emitted
  · rintro ⟨⟨library, libraryMember, nameEqual,
      source, sourceMember, pathEqual⟩, noGraph⟩
    subst rawName
    subst rawPath
    have parsed : CanonicalSourcePath.parse source.path = none :=
      (CanonicalSourcePath.parse_eq_none_iff_no_graph source.path).mpr noGraph
    rw [invalidExternalSourcePathErrors, List.mem_flatMap]
    refine ⟨library, libraryMember, ?_⟩
    rw [List.mem_filterMap]
    exact ⟨source, sourceMember, by simp [parsed]⟩

theorem parseMainFile_eq_some_iff
    (raw : RawSourceFile) (file : WorkspaceFile) :
    parseMainFile raw = some file ↔ MainFileOf raw file := by
  constructor
  · intro execution
    unfold parseMainFile at execution
    cases parsed : CanonicalSourcePath.parse raw.path with
    | none => simp [parsed] at execution
    | some path =>
        simp [parsed] at execution
        subst file
        refine ⟨path, ?_, rfl⟩
        apply parseCanonicalPath_sound
        simpa [parseCanonicalPath] using parsed
  · rintro ⟨path, graph, rfl⟩
    unfold parseMainFile
    have parsed : CanonicalSourcePath.parse raw.path = some path := by
      simpa [parseCanonicalPath] using parseCanonicalPath_complete graph
    simp [parsed]

theorem mem_parsedMainFiles_iff
    (raw : RawWorkspace) (file : WorkspaceFile) :
    file ∈ parsedMainFiles raw ↔
      ∃ source ∈ raw.mainSources, MainFileOf source file := by
  rw [parsedMainFiles, List.mem_filterMap]
  constructor
  · rintro ⟨source, member, execution⟩
    exact ⟨source, member,
      (parseMainFile_eq_some_iff source file).mp execution⟩
  · rintro ⟨source, member, graph⟩
    exact ⟨source, member,
      (parseMainFile_eq_some_iff source file).mpr graph⟩

theorem main_source_id_mem_iff
    (raw : RawWorkspace) (path : CanonicalSourcePath) :
    ({ library := .main, path } : SourceId) ∈ parsedMainFileIds raw ↔
      ∃ source ∈ raw.mainSources, CanonicalPathOf source.path path := by
  constructor
  · intro member
    rw [parsedMainFileIds, List.mem_map] at member
    obtain ⟨file, fileMember, fileId⟩ := member
    rw [mem_parsedMainFiles_iff] at fileMember
    obtain ⟨source, sourceMember, fileGraph⟩ := fileMember
    rcases fileGraph with ⟨sourcePath, pathGraph, rfl⟩
    have pathEqual := congrArg SourceId.path fileId
    simp only at pathEqual
    subst sourcePath
    exact ⟨source, sourceMember, pathGraph⟩
  · rintro ⟨source, sourceMember, pathGraph⟩
    let file : WorkspaceFile := {
      id := { library := .main, path }
      content := source.content
    }
    have fileMember : file ∈ parsedMainFiles raw :=
      (mem_parsedMainFiles_iff raw file).mpr
        ⟨source, sourceMember, path, pathGraph, rfl⟩
    rw [parsedMainFileIds, List.mem_map]
    exact ⟨file, fileMember, rfl⟩

theorem parsedMainFileId_is_main
    {raw : RawWorkspace} {id : SourceId}
    (member : id ∈ parsedMainFileIds raw) :
    id.library = .main := by
  rw [parsedMainFileIds, List.mem_map] at member
  obtain ⟨file, fileMember, rfl⟩ := member
  rw [mem_parsedMainFiles_iff] at fileMember
  obtain ⟨source, _, path, _, rfl⟩ := fileMember
  rfl

theorem parsedMainFileIds_any_entry_iff
    (raw : RawWorkspace) (path : CanonicalSourcePath) :
    (parsedMainFileIds raw).any (fun id =>
      SourceId.compare id { library := .main, path } |>.isEq) = true ↔
      ({ library := .main, path } : SourceId) ∈ parsedMainFileIds raw := by
  constructor
  · intro anyTrue
    obtain ⟨id, member, comparison⟩ := List.any_eq_true.mp anyTrue
    have equal : id = ({ library := .main, path } : SourceId) := by
      apply SourceId.compare_eq_iff_eq.mp
      exact Ordering.isEq_iff_eq_eq.mp comparison
    simpa [equal] using member
  · intro member
    apply List.any_eq_true.mpr
    refine ⟨({ library := .main, path } : SourceId), member, ?_⟩
    simp

theorem mem_missingEntryErrors_iff
    (raw : RawWorkspace) (path : CanonicalSourcePath) :
    .missingEntry path ∈ missingEntryErrors raw ↔
      ValidationError.Applies raw (.missingEntry path) := by
  rw [ValidationError.applies_missingEntry]
  cases parsed : CanonicalSourcePath.parse raw.entry with
  | none =>
      have noGraph :=
        (CanonicalSourcePath.parse_eq_none_iff_no_graph raw.entry).mp parsed
      constructor
      · intro member
        simp [missingEntryErrors, parsed] at member
      · rintro ⟨graph, _⟩
        exact False.elim (noGraph ⟨path, graph⟩)
  | some entryPath =>
      have entryGraph : CanonicalPathOf raw.entry entryPath := by
        apply parseCanonicalPath_sound
        simpa [parseCanonicalPath] using parsed
      cases anyResult : (parsedMainFileIds raw).any (fun id =>
          SourceId.compare id {
            library := .main
            path := entryPath
          } |>.isEq) with
      | false =>
          constructor
          · intro member
            simp [missingEntryErrors, parsed, anyResult] at member
            subst path
            refine ⟨entryGraph, ?_⟩
            rintro ⟨source, sourceMember, sourceGraph⟩
            have idMember := (main_source_id_mem_iff raw entryPath).mpr
              ⟨source, sourceMember, sourceGraph⟩
            have anyTrue := (parsedMainFileIds_any_entry_iff raw entryPath).mpr
              idMember
            rw [anyResult] at anyTrue
            cases anyTrue
          · rintro ⟨graph, noSource⟩
            have pathEqual := CanonicalPathOf.functional graph entryGraph
            subst path
            simp [missingEntryErrors, parsed, anyResult]
      | true =>
          have idMember := (parsedMainFileIds_any_entry_iff raw entryPath).mp
            anyResult
          obtain ⟨source, sourceMember, sourceGraph⟩ :=
            (main_source_id_mem_iff raw entryPath).mp idMember
          constructor
          · intro member
            simp [missingEntryErrors, parsed, anyResult] at member
          · rintro ⟨graph, noSource⟩
            have pathEqual := CanonicalPathOf.functional graph entryGraph
            subst path
            exact False.elim (noSource ⟨source, sourceMember, sourceGraph⟩)

theorem mem_duplicateMainSourcePathErrors_iff
    (raw : RawWorkspace) (path : CanonicalSourcePath) :
    .duplicateMainSourcePath path ∈ duplicateMainSourcePathErrors raw ↔
      ValidationError.Applies raw (.duplicateMainSourcePath path) := by
  rw [ValidationError.applies_duplicateMainSourcePath]
  unfold duplicateMainSourcePathErrors
  rw [mem_duplicateErrors_iff_applied]
  · unfold parsedMainFileIds parsedMainFiles
    rw [atLeastTwo_map_iff, atLeastTwo_filterMap_iff]
    apply atLeastTwo_congr
    intro source
    constructor
    · rintro ⟨file, execution, filePath⟩
      have fileGraph := (parseMainFile_eq_some_iff source file).mp execution
      rcases fileGraph with ⟨parsedPath, pathGraph, rfl⟩
      change ValidationError.duplicateMainSourcePath parsedPath =
        ValidationError.duplicateMainSourcePath path at filePath
      have pathEqual : parsedPath = path := by
        simpa using filePath
      exact pathEqual ▸ pathGraph
    · intro pathGraph
      let file : WorkspaceFile := {
        id := { library := .main, path }
        content := source.content
      }
      exact ⟨file,
        (parseMainFile_eq_some_iff source file).mpr
          ⟨path, pathGraph, rfl⟩,
        rfl⟩
  · intro left right leftMember rightMember equal
    have leftMain := parsedMainFileId_is_main leftMember
    have rightMain := parsedMainFileId_is_main rightMember
    change ValidationError.duplicateMainSourcePath left.path =
      ValidationError.duplicateMainSourcePath right.path at equal
    have pathEqual : left.path = right.path := by
      simpa using equal
    cases left
    cases right
    simp_all

private def parseTaggedExternalFileKey
    (raw : String × RawSourceFile) :
    Option (ExternalLibraryName × CanonicalSourcePath) :=
  match ExternalLibraryName.parse raw.1 with
  | none => none
  | some libraryName =>
      (CanonicalSourcePath.parse raw.2.path).map fun path =>
        (libraryName, path)

private theorem parsedExternalLibraryFileKeys_eq
    (library : RawExternalLibrary) :
    (parseExternalLibraryFiles library).map ParsedExternalFile.key =
      (library.sources.map fun source => (library.name, source)).filterMap
        parseTaggedExternalFileKey := by
  unfold parseExternalLibraryFiles
  cases nameParsed : ExternalLibraryName.parse library.name with
  | none =>
      induction library.sources with
      | nil => simp
      | cons source tail inductionHypothesis =>
          simp [parseTaggedExternalFileKey, nameParsed, inductionHypothesis]
  | some libraryName =>
      induction library.sources with
      | nil => simp
      | cons source tail inductionHypothesis =>
          cases pathParsed : CanonicalSourcePath.parse source.path with
          | none =>
              simp [parseTaggedExternalFileKey, nameParsed, pathParsed,
                inductionHypothesis]
          | some path =>
              simp [parseTaggedExternalFileKey, nameParsed, pathParsed,
                ParsedExternalFile.key, inductionHypothesis]

theorem parsedExternalFileKeys_eq_filterMap_tagged
    (raw : RawWorkspace) :
    parsedExternalFileKeys raw =
      raw.taggedExternalSources.filterMap parseTaggedExternalFileKey := by
  have go : ∀ libraries : List RawExternalLibrary,
      (libraries.flatMap parseExternalLibraryFiles).map
          ParsedExternalFile.key =
        (libraries.flatMap fun library =>
          library.sources.map fun source =>
            (library.name, source)).filterMap parseTaggedExternalFileKey := by
    intro libraries
    induction libraries with
    | nil => simp
    | cons library tail inductionHypothesis =>
        simp [parsedExternalLibraryFileKeys_eq,
          inductionHypothesis, List.map_append]
  simpa [parsedExternalFileKeys, parsedExternalFiles,
    RawWorkspace.taggedExternalSources] using go raw.externalLibraries

theorem parseTaggedExternalFileKey_eq_some_iff
    (raw : String × RawSourceFile)
    (libraryName : ExternalLibraryName) (path : CanonicalSourcePath) :
    parseTaggedExternalFileKey raw = some (libraryName, path) ↔
      ExternalLibraryNameOf raw.1 libraryName ∧
        CanonicalPathOf raw.2.path path := by
  constructor
  · intro execution
    unfold parseTaggedExternalFileKey at execution
    cases nameParsed : ExternalLibraryName.parse raw.1 with
    | none => simp [nameParsed] at execution
    | some parsedName =>
        cases pathParsed : CanonicalSourcePath.parse raw.2.path with
        | none => simp [nameParsed, pathParsed] at execution
        | some parsedPath =>
            simp [nameParsed, pathParsed] at execution
            rcases execution with ⟨nameEqual, pathEqual⟩
            subst parsedName
            subst parsedPath
            exact ⟨ExternalLibraryName.parse_sound nameParsed,
              parseCanonicalPath_sound (by
                simpa [parseCanonicalPath] using pathParsed)⟩
  · rintro ⟨nameGraph, pathGraph⟩
    unfold parseTaggedExternalFileKey
    have nameParsed := ExternalLibraryName.parse_complete nameGraph
    have pathParsed : CanonicalSourcePath.parse raw.2.path = some path := by
      simpa [parseCanonicalPath] using parseCanonicalPath_complete pathGraph
    simp [nameParsed, pathParsed]

private def selectTaggedExternalSource (rawName : String)
    (tagged : String × RawSourceFile) : Option RawSourceFile :=
  if tagged.1 = rawName then some tagged.2 else none

private theorem externalSourcesNamed_eq_filterMap_tagged
    (raw : RawWorkspace) (rawName : String) :
    raw.externalSourcesNamed rawName =
      raw.taggedExternalSources.filterMap
        (selectTaggedExternalSource rawName) := by
  unfold RawWorkspace.externalSourcesNamed
    RawWorkspace.taggedExternalSources
  induction raw.externalLibraries with
  | nil => simp
  | cons library tail inductionHypothesis =>
      by_cases equal : library.name = rawName
      · simp [equal, selectTaggedExternalSource, Function.comp_def,
          inductionHypothesis]
      · simp [equal, selectTaggedExternalSource, Function.comp_def,
          inductionHypothesis]

theorem atLeastTwo_externalSourcesNamed_iff
    (raw : RawWorkspace) (rawName : String)
    (predicate : RawSourceFile -> Prop) :
    AtLeastTwo (raw.externalSourcesNamed rawName) predicate ↔
      AtLeastTwo raw.taggedExternalSources (fun tagged =>
        tagged.1 = rawName ∧ predicate tagged.2) := by
  rw [externalSourcesNamed_eq_filterMap_tagged,
    atLeastTwo_filterMap_iff]
  apply atLeastTwo_congr
  intro tagged
  constructor
  · rintro ⟨output, execution, holds⟩
    unfold selectTaggedExternalSource at execution
    split at execution
    · rename_i nameEqual
      simp at execution
      subst output
      exact ⟨nameEqual, holds⟩
    · simp at execution
  · rintro ⟨nameEqual, holds⟩
    exact ⟨tagged.2, by
      simp [selectTaggedExternalSource, nameEqual], holds⟩

theorem mem_duplicateExternalSourcePathErrors_iff
    (raw : RawWorkspace) (libraryName : ExternalLibraryName)
    (path : CanonicalSourcePath) :
    .duplicateExternalSourcePath libraryName path ∈
        duplicateExternalSourcePathErrors raw ↔
      ValidationError.Applies raw
        (.duplicateExternalSourcePath libraryName path) := by
  rw [ValidationError.applies_duplicateExternalSourcePath]
  unfold duplicateExternalSourcePathErrors
  rw [mem_duplicateErrors_iff_applied]
  · rw [parsedExternalFileKeys_eq_filterMap_tagged,
      atLeastTwo_filterMap_iff]
    change
      (AtLeastTwo raw.taggedExternalSources (fun tagged =>
        ∃ output,
          parseTaggedExternalFileKey tagged = some output ∧
            ValidationError.duplicateExternalSourcePath output.1 output.2 =
              .duplicateExternalSourcePath libraryName path) ↔ _)
    have parsedPredicate :
        AtLeastTwo raw.taggedExternalSources (fun tagged =>
          ∃ output,
            parseTaggedExternalFileKey tagged = some output ∧
              ValidationError.duplicateExternalSourcePath output.1 output.2 =
                .duplicateExternalSourcePath libraryName path) ↔
          AtLeastTwo raw.taggedExternalSources (fun tagged =>
            ExternalLibraryNameOf tagged.1 libraryName ∧
              CanonicalPathOf tagged.2.path path) := by
      apply atLeastTwo_congr
      intro tagged
      constructor
      · rintro ⟨⟨parsedName, parsedPath⟩, parsed, errorEqual⟩
        simp only [ValidationError.duplicateExternalSourcePath.injEq] at errorEqual
        rcases errorEqual with ⟨nameEqual, pathEqual⟩
        subst parsedName
        subst parsedPath
        exact (parseTaggedExternalFileKey_eq_some_iff
          tagged libraryName path).mp parsed
      · intro graphs
        exact ⟨(libraryName, path),
          (parseTaggedExternalFileKey_eq_some_iff
            tagged libraryName path).mpr graphs,
          rfl⟩
    rw [parsedPredicate]
    constructor
    · intro repeated
      have named : AtLeastTwo (raw.externalSourcesNamed libraryName.render)
          (fun source => CanonicalPathOf source.path path) := by
        rw [atLeastTwo_externalSourcesNamed_iff]
        exact (atLeastTwo_congr fun tagged => by
          rw [ExternalLibraryNameOf.iff_eq_render]).mpr repeated
      exact ⟨libraryName.render, .rendered libraryName, named⟩
    · rintro ⟨rawName, nameGraph, repeated⟩
      have nameEqual := ExternalLibraryNameOf.iff_eq_render.mp nameGraph
      subst rawName
      rw [atLeastTwo_externalSourcesNamed_iff] at repeated
      exact (atLeastTwo_congr fun tagged => by
        rw [ExternalLibraryNameOf.iff_eq_render]).mp repeated
  · intro left right _ _ equal
    change ValidationError.duplicateExternalSourcePath left.1 left.2 =
      ValidationError.duplicateExternalSourcePath right.1 right.2 at equal
    have components : left.1 = right.1 ∧ left.2 = right.2 := by
      simpa using equal
    exact Prod.ext components.1 components.2

private theorem invalidEntryPathErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ invalidEntryPathErrors raw) :
    ValidationError.Applies raw error := by
  cases parsed : CanonicalSourcePath.parse raw.entry with
  | none =>
      have equal : error = .invalidEntryPath raw.entry := by
        simpa [invalidEntryPathErrors, parsed] using member
      subst error
      exact (mem_invalidEntryPathErrors_iff raw raw.entry).mp member
  | some path => simp [invalidEntryPathErrors, parsed] at member

private theorem invalidExternalLibraryNameErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ invalidExternalLibraryNameErrors raw) :
    ValidationError.Applies raw error := by
  rw [invalidExternalLibraryNameErrors, List.mem_filterMap] at member
  obtain ⟨library, libraryMember, emitted⟩ := member
  cases parsed : ExternalLibraryName.parse library.name with
  | none =>
      simp [parsed] at emitted
      subst error
      apply (mem_invalidExternalLibraryNameErrors_iff raw library.name).mp
      rw [invalidExternalLibraryNameErrors, List.mem_filterMap]
      exact ⟨library, libraryMember, by simp [parsed]⟩
  | some name => simp [parsed] at emitted

private theorem duplicateExternalLibraryNameErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ duplicateExternalLibraryNameErrors raw) :
    ValidationError.Applies raw error := by
  unfold duplicateExternalLibraryNameErrors at member
  rw [mem_duplicateErrors_iff] at member
  obtain ⟨rawName, emitted, repeated⟩ := member
  subst error
  apply (mem_duplicateExternalLibraryNameErrors_iff raw rawName).mp
  unfold duplicateExternalLibraryNameErrors
  rw [mem_duplicateErrors_iff]
  exact ⟨rawName, rfl, repeated⟩

private theorem invalidMainSourcePathErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ invalidMainSourcePathErrors raw) :
    ValidationError.Applies raw error := by
  rw [invalidMainSourcePathErrors, List.mem_filterMap] at member
  obtain ⟨source, sourceMember, emitted⟩ := member
  cases parsed : CanonicalSourcePath.parse source.path with
  | none =>
      simp [parsed] at emitted
      subst error
      apply (mem_invalidMainSourcePathErrors_iff raw source.path).mp
      rw [invalidMainSourcePathErrors, List.mem_filterMap]
      exact ⟨source, sourceMember, by simp [parsed]⟩
  | some path => simp [parsed] at emitted

private theorem invalidExternalSourcePathErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ invalidExternalSourcePathErrors raw) :
    ValidationError.Applies raw error := by
  rw [invalidExternalSourcePathErrors, List.mem_flatMap] at member
  obtain ⟨library, libraryMember, sourceMember⟩ := member
  rw [List.mem_filterMap] at sourceMember
  obtain ⟨source, rawSourceMember, emitted⟩ := sourceMember
  cases parsed : CanonicalSourcePath.parse source.path with
  | none =>
      simp [parsed] at emitted
      subst error
      apply (mem_invalidExternalSourcePathErrors_iff
        raw library.name source.path).mp
      rw [invalidExternalSourcePathErrors, List.mem_flatMap]
      refine ⟨library, libraryMember, ?_⟩
      rw [List.mem_filterMap]
      exact ⟨source, rawSourceMember, by simp [parsed]⟩
  | some path => simp [parsed] at emitted

private theorem duplicateMainSourcePathErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ duplicateMainSourcePathErrors raw) :
    ValidationError.Applies raw error := by
  unfold duplicateMainSourcePathErrors at member
  rw [mem_duplicateErrors_iff] at member
  obtain ⟨id, emitted, repeated⟩ := member
  change ValidationError.duplicateMainSourcePath id.path = error at emitted
  subst error
  apply (mem_duplicateMainSourcePathErrors_iff raw id.path).mp
  unfold duplicateMainSourcePathErrors
  rw [mem_duplicateErrors_iff]
  exact ⟨id, rfl, repeated⟩

private theorem duplicateExternalSourcePathErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ duplicateExternalSourcePathErrors raw) :
    ValidationError.Applies raw error := by
  unfold duplicateExternalSourcePathErrors at member
  rw [mem_duplicateErrors_iff] at member
  obtain ⟨key, emitted, repeated⟩ := member
  change ValidationError.duplicateExternalSourcePath key.1 key.2 = error at emitted
  subst error
  apply (mem_duplicateExternalSourcePathErrors_iff raw key.1 key.2).mp
  unfold duplicateExternalSourcePathErrors
  rw [mem_duplicateErrors_iff]
  exact ⟨key, rfl, repeated⟩

private theorem missingEntryErrors_sound
    {raw : RawWorkspace} {error : ValidationError}
    (member : error ∈ missingEntryErrors raw) :
    ValidationError.Applies raw error := by
  cases parsed : CanonicalSourcePath.parse raw.entry with
  | none => simp [missingEntryErrors, parsed] at member
  | some path =>
      cases present : (parsedMainFileIds raw).any (fun id =>
          SourceId.compare id { library := .main, path } |>.isEq) with
      | false =>
          have equal : error = .missingEntry path := by
            simpa [missingEntryErrors, parsed, present] using member
          subst error
          exact (mem_missingEntryErrors_iff raw path).mp member
      | true => simp [missingEntryErrors, parsed, present] at member

/-- The executable candidate stream contains exactly the applicable errors. -/
theorem mem_errorCandidates_iff
    (raw : RawWorkspace) (error : ValidationError) :
    error ∈ errorCandidates raw ↔ ValidationError.Applies raw error := by
  constructor
  · intro member
    unfold errorCandidates at member
    rcases List.mem_append.mp member with firstSeven | eighth
    · rcases List.mem_append.mp firstSeven with firstSix | seventh
      · rcases List.mem_append.mp firstSix with firstFive | sixth
        · rcases List.mem_append.mp firstFive with firstFour | fifth
          · rcases List.mem_append.mp firstFour with firstThree | fourth
            · rcases List.mem_append.mp firstThree with firstTwo | third
              · rcases List.mem_append.mp firstTwo with first | second
                · exact invalidEntryPathErrors_sound first
                · exact invalidExternalLibraryNameErrors_sound second
              · exact duplicateExternalLibraryNameErrors_sound third
            · exact invalidMainSourcePathErrors_sound fourth
          · exact invalidExternalSourcePathErrors_sound fifth
        · exact duplicateMainSourcePathErrors_sound sixth
      · exact duplicateExternalSourcePathErrors_sound seventh
    · exact missingEntryErrors_sound eighth
  · intro applies
    simp only [errorCandidates, List.mem_append]
    cases error with
    | invalidEntryPath rawEntry =>
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          ((mem_invalidEntryPathErrors_iff raw rawEntry).mpr applies)))))))
    | invalidExternalLibraryName rawName =>
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          ((mem_invalidExternalLibraryNameErrors_iff raw rawName).mpr applies)))))))
    | duplicateExternalLibraryName rawName =>
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          ((mem_duplicateExternalLibraryNameErrors_iff raw rawName).mpr applies))))))
    | invalidMainSourcePath rawPath =>
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
          ((mem_invalidMainSourcePathErrors_iff raw rawPath).mpr applies)))))
    | invalidExternalSourcePath rawName rawPath =>
        exact Or.inl (Or.inl (Or.inl (Or.inr
          ((mem_invalidExternalSourcePathErrors_iff
            raw rawName rawPath).mpr applies))))
    | duplicateMainSourcePath path =>
        exact Or.inl (Or.inl (Or.inr
          ((mem_duplicateMainSourcePathErrors_iff raw path).mpr applies)))
    | duplicateExternalSourcePath name path =>
        exact Or.inl (Or.inr
          ((mem_duplicateExternalSourcePathErrors_iff
            raw name path).mpr applies))
    | missingEntry path =>
        exact Or.inr ((mem_missingEntryErrors_iff raw path).mpr applies)

/-- The canonical executable list contains exactly the declarative errors. -/
theorem validationError_applies_iff_mem
    (raw : RawWorkspace) (error : ValidationError) :
    ValidationError.Applies raw error ↔ error ∈ validationErrors raw := by
  rw [mem_validationErrors, mem_errorCandidates_iff]

/-- The executable diagnostic list realizes the canonical error judgment. -/
theorem validationErrors_for (raw : RawWorkspace) :
    ValidationErrorsFor raw (validationErrors raw) where
  sorted := by
    change (validationErrors raw).Pairwise fun left right =>
      ValidationError.compare left right = .lt
    exact validationErrors_strictlySorted raw
  unique := validationErrors_nodup raw
  applies_iff_mem := fun error =>
    (validationError_applies_iff_mem raw error).symm

/-- Executable success is exactly absence of every declarative error. -/
theorem noValidationErrorApplies_iff_validationErrors_eq_nil
    (raw : RawWorkspace) :
    NoValidationErrorApplies raw ↔ validationErrors raw = [] := by
  constructor
  · intro noErrors
    rw [List.eq_nil_iff_forall_not_mem]
    intro error member
    exact noErrors error
      ((validationError_applies_iff_mem raw error).mpr member)
  · intro errorsNil error applies
    have member :=
      (validationError_applies_iff_mem raw error).mp applies
    simp [errorsNil] at member

end Validation

namespace RawWorkspace

/-- Tagged-source membership exposes its originating external declaration. -/
theorem mem_taggedExternalSources_iff
    (raw : RawWorkspace) (rawName : String) (source : RawSourceFile) :
    (rawName, source) ∈ raw.taggedExternalSources ↔
      ∃ library ∈ raw.externalLibraries,
        library.name = rawName ∧ source ∈ library.sources := by
  unfold taggedExternalSources
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨library, libraryMember, taggedMember⟩
    rw [List.mem_map] at taggedMember
    obtain ⟨original, sourceMember, equal⟩ := taggedMember
    have components : library.name = rawName ∧ original = source := by
      simpa using equal
    exact ⟨library, libraryMember, components.1,
      components.2 ▸ sourceMember⟩
  · rintro ⟨library, libraryMember, nameEqual, sourceMember⟩
    refine ⟨library, libraryMember, ?_⟩
    rw [List.mem_map]
    exact ⟨source, sourceMember, by simp [nameEqual]⟩

/-- Nested raw external-source occurrence is equivalent to tagged occurrence. -/
theorem externalSourceOccurs_iff_tagged
    (raw : RawWorkspace) (rawName rawPath : String) :
    (∃ library ∈ raw.externalLibraries,
      library.name = rawName ∧
        ∃ source ∈ library.sources, source.path = rawPath) ↔
      ∃ tagged ∈ raw.taggedExternalSources,
        tagged.1 = rawName ∧ tagged.2.path = rawPath := by
  constructor
  · rintro ⟨library, libraryMember, nameEqual,
      source, sourceMember, pathEqual⟩
    exact ⟨(library.name, source),
      (mem_taggedExternalSources_iff raw library.name source).mpr
        ⟨library, libraryMember, rfl, sourceMember⟩,
      nameEqual, pathEqual⟩
  · rintro ⟨⟨taggedName, source⟩, taggedMember,
      nameEqual, pathEqual⟩
    obtain ⟨library, libraryMember, libraryNameEqual, sourceMember⟩ :=
      (mem_taggedExternalSources_iff raw taggedName source).mp taggedMember
    exact ⟨library, libraryMember,
      libraryNameEqual.trans nameEqual, source, sourceMember, pathEqual⟩

end RawWorkspace

namespace ValidationError

/-- Raw-workspace equivalence preserves every declarative error condition. -/
theorem applies_equivalent_iff {left right : RawWorkspace}
    (equivalent : left.Equivalent right) (error : ValidationError) :
    Applies left error ↔ Applies right error := by
  cases error with
  | invalidEntryPath rawEntry =>
      simp only [applies_invalidEntryPath]
      rw [equivalent.entry_eq]
  | invalidExternalLibraryName rawName =>
      simp only [applies_invalidExternalLibraryName]
      have occurs :
          (∃ library ∈ left.externalLibraries,
            library.name = rawName) ↔
            ∃ library ∈ right.externalLibraries,
              library.name = rawName := by
        calc
          (∃ library ∈ left.externalLibraries,
              library.name = rawName) ↔
              rawName ∈ left.externalLibraries.map RawExternalLibrary.name := by
                simp
          _ ↔ rawName ∈
              right.externalLibraries.map RawExternalLibrary.name :=
                equivalent.externalLibraryNames_perm.mem_iff
          _ ↔ (∃ library ∈ right.externalLibraries,
              library.name = rawName) := by
                simp
      exact and_congr occurs Iff.rfl
  | duplicateExternalLibraryName rawName =>
      simp only [applies_duplicateExternalLibraryName]
      calc
        AtLeastTwo left.externalLibraries
            (fun library => library.name = rawName) ↔
            AtLeastTwo
              (left.externalLibraries.map RawExternalLibrary.name)
              (fun name => name = rawName) :=
          (atLeastTwo_map_iff RawExternalLibrary.name
            (fun name => name = rawName) left.externalLibraries).symm
        _ ↔ AtLeastTwo
              (right.externalLibraries.map RawExternalLibrary.name)
              (fun name => name = rawName) :=
          atLeastTwo_perm_iff equivalent.externalLibraryNames_perm _
        _ ↔ AtLeastTwo right.externalLibraries
            (fun library => library.name = rawName) :=
          atLeastTwo_map_iff RawExternalLibrary.name
            (fun name => name = rawName) right.externalLibraries
  | invalidMainSourcePath rawPath =>
      simp only [applies_invalidMainSourcePath]
      exact and_congr
        (exists_mem_perm_iff equivalent.mainSources_perm
          (fun source => source.path = rawPath)) Iff.rfl
  | invalidExternalSourcePath rawName rawPath =>
      simp only [applies_invalidExternalSourcePath]
      have occurs :
          (∃ library ∈ left.externalLibraries,
            library.name = rawName ∧
              ∃ source ∈ library.sources,
                source.path = rawPath) ↔
            ∃ library ∈ right.externalLibraries,
              library.name = rawName ∧
                ∃ source ∈ library.sources,
                  source.path = rawPath := by
        rw [left.externalSourceOccurs_iff_tagged,
          right.externalSourceOccurs_iff_tagged]
        exact exists_mem_perm_iff
          equivalent.taggedExternalSources_perm
          (fun tagged =>
            tagged.1 = rawName ∧ tagged.2.path = rawPath)
      exact and_congr occurs Iff.rfl
  | duplicateMainSourcePath path =>
      simp only [applies_duplicateMainSourcePath]
      exact atLeastTwo_perm_iff equivalent.mainSources_perm
        (fun source => CanonicalPathOf source.path path)
  | duplicateExternalSourcePath libraryName path =>
      simp only [applies_duplicateExternalSourcePath]
      constructor
      · rintro ⟨rawName, nameGraph, repeated⟩
        refine ⟨rawName, nameGraph, ?_⟩
        rw [Validation.atLeastTwo_externalSourcesNamed_iff] at repeated ⊢
        exact (atLeastTwo_perm_iff
          equivalent.taggedExternalSources_perm _).mp repeated
      · rintro ⟨rawName, nameGraph, repeated⟩
        refine ⟨rawName, nameGraph, ?_⟩
        rw [Validation.atLeastTwo_externalSourcesNamed_iff] at repeated ⊢
        exact (atLeastTwo_perm_iff
          equivalent.taggedExternalSources_perm _).mpr repeated
  | missingEntry path =>
      simp only [applies_missingEntry]
      rw [equivalent.entry_eq]
      exact and_congr Iff.rfl (not_congr
        (exists_mem_perm_iff equivalent.mainSources_perm
          (fun source => CanonicalPathOf source.path path)))

end ValidationError

namespace NoValidationErrorApplies

/-- Raw-workspace equivalence preserves absence of validation errors. -/
theorem equivalent_iff {left right : RawWorkspace}
    (equivalent : left.Equivalent right) :
    NoValidationErrorApplies left ↔ NoValidationErrorApplies right := by
  constructor
  · intro noErrors error applies
    exact noErrors error
      ((ValidationError.applies_equivalent_iff equivalent error).mpr applies)
  · intro noErrors error applies
    exact noErrors error
      ((ValidationError.applies_equivalent_iff equivalent error).mp applies)

end NoValidationErrorApplies

namespace ValidationErrorsFor

/-- Raw-workspace equivalence preserves the canonical error-list judgment. -/
theorem equivalent_iff {left right : RawWorkspace}
    (equivalent : left.Equivalent right) (errors : List ValidationError) :
    ValidationErrorsFor left errors ↔ ValidationErrorsFor right errors := by
  constructor
  · intro errorsFor
    exact {
      sorted := errorsFor.sorted
      unique := errorsFor.unique
      applies_iff_mem := fun error => by
        rw [errorsFor.applies_iff_mem]
        exact ValidationError.applies_equivalent_iff equivalent error
    }
  · intro errorsFor
    exact {
      sorted := errorsFor.sorted
      unique := errorsFor.unique
      applies_iff_mem := fun error => by
        rw [errorsFor.applies_iff_mem]
        exact (ValidationError.applies_equivalent_iff equivalent error).symm
    }

end ValidationErrorsFor

namespace Rejects

/-- Raw-workspace equivalence preserves declarative rejection. -/
theorem equivalent_iff {left right : RawWorkspace}
    (equivalent : left.Equivalent right) (errors : List ValidationError) :
    Rejects left errors ↔ Rejects right errors := by
  constructor
  · intro rejects
    exact {
      errorsFor :=
        (ValidationErrorsFor.equivalent_iff equivalent errors).mp
          rejects.errorsFor
      nonempty := rejects.nonempty
    }
  · intro rejects
    exact {
      errorsFor :=
        (ValidationErrorsFor.equivalent_iff equivalent errors).mpr
          rejects.errorsFor
      nonempty := rejects.nonempty
    }

end Rejects

namespace Validates

private theorem equivalent_forward {left right : RawWorkspace}
    (equivalent : left.Equivalent right)
    {workspace : ValidatedUserWorkspace}
    (validates : Validates left workspace) :
    Validates right workspace := by
  rcases validates with
    ⟨relational, noErrors, entryGraph, entryEqual,
      mainGraph, namesGraph, externalGraph,
      declaredLibraries, files⟩
  obtain ⟨rightMainFiles, mainPermutation, rightMainGraph⟩ :=
    ListCorresponds.transport_perm equivalent.mainSources_perm mainGraph
  obtain ⟨rightNames, namesPermutation, rightNamesGraph⟩ :=
    ListCorresponds.transport_perm
      equivalent.externalLibraryNames_perm namesGraph
  obtain ⟨rightExternalFiles, externalPermutation, rightExternalGraph⟩ :=
    ListCorresponds.transport_perm
      equivalent.taggedExternalSources_perm externalGraph
  let rightRelational : RelationalUserWorkspace := {
    entryPath := relational.entryPath
    mainFiles := rightMainFiles
    externalLibraryNames := rightNames
    externalFiles := rightExternalFiles
  }
  refine ⟨rightRelational,
    (NoValidationErrorApplies.equivalent_iff equivalent).mp noErrors,
    ?_, entryEqual, rightMainGraph, rightNamesGraph, rightExternalGraph,
    declaredLibraries.trans namesPermutation,
    files.trans (mainPermutation.append externalPermutation)⟩
  rw [← equivalent.entry_eq]
  exact entryGraph

/-- Raw-workspace equivalence preserves declarative successful validation. -/
theorem equivalent_iff {left right : RawWorkspace}
    (equivalent : left.Equivalent right)
    (workspace : ValidatedUserWorkspace) :
    Validates left workspace ↔ Validates right workspace := by
  constructor
  · exact equivalent_forward equivalent
  · exact equivalent_forward
      (RawWorkspace.equivalent_symm equivalent)

end Validates

namespace Validation

/-- Equivalent raw workspaces have the same complete canonical errors. -/
theorem validationErrors_equivalent {left right : RawWorkspace}
    (equivalent : left.Equivalent right) :
    validationErrors left = validationErrors right := by
  apply ValidationErrorsFor.functional
    (workspace := right)
    (first := validationErrors left)
    (second := validationErrors right)
  · exact (ValidationErrorsFor.equivalent_iff equivalent _).mp
      (validationErrors_for left)
  · exact validationErrors_for right

private def parseTaggedExternalFile
    (raw : String × RawSourceFile) : Option WorkspaceFile :=
  match ExternalLibraryName.parse raw.1 with
  | none => none
  | some libraryName =>
      (CanonicalSourcePath.parse raw.2.path).map fun path => {
        id := { library := .external libraryName, path }
        content := raw.2.content
      }

private theorem parseTaggedExternalFile_eq_some_iff
    (raw : String × RawSourceFile) (file : WorkspaceFile) :
    parseTaggedExternalFile raw = some file ↔
      TaggedExternalFileOf raw file := by
  constructor
  · intro execution
    unfold parseTaggedExternalFile at execution
    cases nameParsed : ExternalLibraryName.parse raw.1 with
    | none => simp [nameParsed] at execution
    | some libraryName =>
        cases pathParsed : CanonicalSourcePath.parse raw.2.path with
        | none => simp [nameParsed, pathParsed] at execution
        | some path =>
            simp [nameParsed, pathParsed] at execution
            subst file
            exact ⟨libraryName, path,
              ExternalLibraryName.parse_sound nameParsed,
              parseCanonicalPath_sound (by
                simpa [parseCanonicalPath] using pathParsed),
              rfl⟩
  · rintro ⟨libraryName, path, nameGraph, pathGraph, rfl⟩
    unfold parseTaggedExternalFile
    have nameParsed : ExternalLibraryName.parse raw.1 =
        some libraryName := ExternalLibraryName.parse_complete nameGraph
    have pathParsed : CanonicalSourcePath.parse raw.2.path = some path := by
      simpa [parseCanonicalPath] using parseCanonicalPath_complete pathGraph
    simp [nameParsed, pathParsed]

private theorem parsedExternalLibraryWorkspaceFiles_eq
    (library : RawExternalLibrary) :
    (parseExternalLibraryFiles library).map
        ParsedExternalFile.toWorkspaceFile =
      (library.sources.map fun source =>
        (library.name, source)).filterMap parseTaggedExternalFile := by
  unfold parseExternalLibraryFiles
  cases nameParsed : ExternalLibraryName.parse library.name with
  | none =>
      induction library.sources with
      | nil => simp
      | cons source tail inductionHypothesis =>
          simp [parseTaggedExternalFile, nameParsed, inductionHypothesis]
  | some libraryName =>
      induction library.sources with
      | nil => simp
      | cons source tail inductionHypothesis =>
          cases pathParsed : CanonicalSourcePath.parse source.path with
          | none =>
              simp [parseTaggedExternalFile, nameParsed, pathParsed,
                inductionHypothesis]
          | some path =>
              simp [parseTaggedExternalFile, nameParsed, pathParsed,
                ParsedExternalFile.toWorkspaceFile, inductionHypothesis]

private theorem parsedExternalWorkspaceFiles_eq_filterMap_tagged
    (raw : RawWorkspace) :
    (parsedExternalFiles raw).map ParsedExternalFile.toWorkspaceFile =
      raw.taggedExternalSources.filterMap parseTaggedExternalFile := by
  have go : ∀ libraries : List RawExternalLibrary,
      (libraries.flatMap parseExternalLibraryFiles).map
          ParsedExternalFile.toWorkspaceFile =
        (libraries.flatMap fun library =>
          library.sources.map fun source =>
            (library.name, source)).filterMap parseTaggedExternalFile := by
    intro libraries
    induction libraries with
    | nil => simp
    | cons library tail inductionHypothesis =>
        simp [parsedExternalLibraryWorkspaceFiles_eq,
          inductionHypothesis, List.map_append]
  simpa [parsedExternalFiles, RawWorkspace.taggedExternalSources] using
    go raw.externalLibraries

private theorem mainFilesOf_parsedMainFiles
    (raw : RawWorkspace) (noErrors : NoValidationErrorApplies raw) :
    MainFilesOf raw.mainSources (parsedMainFiles raw) := by
  unfold MainFilesOf parsedMainFiles
  apply ListCorresponds.filterMap_of_total MainFileOf parseMainFile
    (fun graph => (parseMainFile_eq_some_iff _ _).mpr graph)
  intro source sourceMember
  by_cases graphExists : ∃ path, CanonicalPathOf source.path path
  · obtain ⟨path, pathGraph⟩ := graphExists
    exact ⟨{
      id := { library := .main, path }
      content := source.content
    }, path, pathGraph, rfl⟩
  · exact False.elim (noErrors (.invalidMainSourcePath source.path)
      ⟨⟨source, sourceMember, rfl⟩, graphExists⟩)

private theorem externalLibraryNamesOf_parsedExternalLibraryNames
    (raw : RawWorkspace) (noErrors : NoValidationErrorApplies raw) :
    ExternalLibraryNamesOf
      (raw.externalLibraries.map RawExternalLibrary.name)
      (parsedExternalLibraryNames raw) := by
  unfold ExternalLibraryNamesOf parsedExternalLibraryNames
  apply ListCorresponds.filterMap_of_total
    ExternalLibraryNameOf ExternalLibraryName.parse
    (fun graph => (ExternalLibraryName.parse_eq_some_iff_graph _ _).mpr graph)
  intro rawName nameMember
  by_cases graphExists : ∃ name, ExternalLibraryNameOf rawName name
  · exact graphExists
  · have occurs : ∃ library ∈ raw.externalLibraries,
        library.name = rawName := by
      rw [List.mem_map] at nameMember
      obtain ⟨library, libraryMember, nameEqual⟩ := nameMember
      exact ⟨library, libraryMember, nameEqual⟩
    exact False.elim
      (noErrors (.invalidExternalLibraryName rawName)
        ⟨occurs, graphExists⟩)

private theorem taggedExternalFilesOf_parsedExternalFiles
    (raw : RawWorkspace) (noErrors : NoValidationErrorApplies raw) :
    TaggedExternalFilesOf raw.taggedExternalSources
      ((parsedExternalFiles raw).map
        ParsedExternalFile.toWorkspaceFile) := by
  rw [parsedExternalWorkspaceFiles_eq_filterMap_tagged]
  unfold TaggedExternalFilesOf
  apply ListCorresponds.filterMap_of_total
    TaggedExternalFileOf parseTaggedExternalFile
    (fun graph => (parseTaggedExternalFile_eq_some_iff _ _).mpr graph)
  intro tagged taggedMember
  obtain ⟨library, libraryMember, libraryNameEqual, sourceMember⟩ :=
    (RawWorkspace.mem_taggedExternalSources_iff
      raw tagged.1 tagged.2).mp taggedMember
  by_cases nameGraphExists :
      ∃ name, ExternalLibraryNameOf tagged.1 name
  · obtain ⟨name, nameGraph⟩ := nameGraphExists
    by_cases pathGraphExists :
        ∃ path, CanonicalPathOf tagged.2.path path
    · obtain ⟨path, pathGraph⟩ := pathGraphExists
      exact ⟨{
        id := { library := .external name, path }
        content := tagged.2.content
      }, name, path, nameGraph, pathGraph, rfl⟩
    · exact False.elim
        (noErrors (.invalidExternalSourcePath tagged.1 tagged.2.path)
          ⟨⟨library, libraryMember, libraryNameEqual,
            tagged.2, sourceMember, rfl⟩,
            pathGraphExists⟩)
  · have occurs : ∃ candidate ∈ raw.externalLibraries,
        candidate.name = tagged.1 :=
      ⟨library, libraryMember, libraryNameEqual⟩
    exact False.elim
      (noErrors (.invalidExternalLibraryName tagged.1)
        ⟨occurs, nameGraphExists⟩)

/-- The executable canonical constructor satisfies the declarative judgment. -/
theorem buildValidatedWorkspace_validates
    (raw : RawWorkspace) (candidatesNil : errorCandidates raw = []) :
    Validates raw (buildValidatedWorkspace raw candidatesNil) := by
  have errorsNil : validationErrors raw = [] :=
    (validationErrors_eq_nil_iff raw).mpr candidatesNil
  have noErrors : NoValidationErrorApplies raw :=
    (noValidationErrorApplies_iff_validationErrors_eq_nil raw).mpr errorsNil
  let relational : RelationalUserWorkspace := {
    entryPath := (buildValidatedWorkspace raw candidatesNil).entry.path
    mainFiles := parsedMainFiles raw
    externalLibraryNames := parsedExternalLibraryNames raw
    externalFiles := (parsedExternalFiles raw).map
      ParsedExternalFile.toWorkspaceFile
  }
  refine ⟨relational, noErrors, ?_, ?_,
    mainFilesOf_parsedMainFiles raw noErrors,
    externalLibraryNamesOf_parsedExternalLibraryNames raw noErrors,
    taggedExternalFilesOf_parsedExternalFiles raw noErrors,
    ?_, ?_⟩
  · dsimp [relational]
    apply parseCanonicalPath_sound
    simpa [parseCanonicalPath] using
      buildValidatedWorkspace_entry_parsed raw candidatesNil
  · dsimp [relational]
    cases entryEqual : (buildValidatedWorkspace raw candidatesNil).entry with
    | mk library path =>
        have libraryEqual : library = .main := by
          simpa [entryEqual] using
            (buildValidatedWorkspace raw candidatesNil).entryIsMain
        subst library
        rfl
  · dsimp [relational]
    unfold canonicalExternalLibraryNames
    exact List.mergeSort_perm (parsedExternalLibraryNames raw)
      ExternalLibraryName.le
  · dsimp [relational]
    unfold canonicalWorkspaceFiles parsedWorkspaceFiles
    exact List.mergeSort_perm
      (parsedMainFiles raw ++
        (parsedExternalFiles raw).map ParsedExternalFile.toWorkspaceFile)
      WorkspaceFile.leById

/-- Every executable success satisfies the independent validation judgment. -/
theorem validate_sound {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (accepted : validate raw = .ok workspace) :
    Validates raw workspace := by
  by_cases errorsNil : validationErrors raw = []
  · have execution := validate_eq_ok_of_validationErrors_eq_nil errorsNil
    rw [accepted] at execution
    injection execution with workspaceEqual
    subst workspace
    exact buildValidatedWorkspace_validates raw
      ((validationErrors_eq_nil_iff raw).mp errorsNil)
  · have rejected := validate_eq_error_of_validationErrors_ne_nil errorsNil
    rw [accepted] at rejected
    cases rejected

/-- Every declaratively valid workspace is returned by the executor. -/
theorem validate_complete {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (validates : Validates raw workspace) :
    validate raw = .ok workspace := by
  rcases validates with ⟨relational, noErrors, rest⟩
  have errorsNil : validationErrors raw = [] :=
    (noValidationErrorApplies_iff_validationErrors_eq_nil raw).mp noErrors
  have canonicalValidates := buildValidatedWorkspace_validates raw
    ((validationErrors_eq_nil_iff raw).mp errorsNil)
  have workspaceEqual :
      buildValidatedWorkspace raw
          ((validationErrors_eq_nil_iff raw).mp errorsNil) = workspace :=
    Validates.functional canonicalValidates ⟨relational, noErrors, rest⟩
  rw [validate_eq_ok_of_validationErrors_eq_nil errorsNil, workspaceEqual]

/-- Every executable error result satisfies declarative rejection. -/
theorem validate_errors_sound {raw : RawWorkspace}
    {errors : List ValidationError}
    (rejected : validate raw = .error errors) :
    Rejects raw errors := by
  obtain ⟨errorsEqual, nonempty⟩ := (validate_eq_error_iff).mp rejected
  subst errors
  exact {
    errorsFor := validationErrors_for raw
    nonempty
  }

/-- Every declarative rejection is returned by the executor. -/
theorem validate_errors_complete {raw : RawWorkspace}
    {errors : List ValidationError}
    (rejects : Rejects raw errors) :
    validate raw = .error errors := by
  have errorsEqual : validationErrors raw = errors :=
    ValidationErrorsFor.functional (validationErrors_for raw)
      rejects.errorsFor
  exact (validate_eq_error_iff).mpr ⟨errorsEqual, rejects.nonempty⟩

end Validation

export Validation
  (validate_sound validate_complete
    validate_errors_sound validate_errors_complete)

namespace Validates

/-- Successful and rejected declarative judgments are mutually exclusive. -/
theorem not_rejected {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace} {errors : List ValidationError}
    (validates : Validates raw workspace) :
    ¬Rejects raw errors := by
  rcases validates with ⟨_, noErrors, _⟩
  intro rejects
  cases errors with
  | nil => exact rejects.nonempty rfl
  | cons error rest =>
      have applies := (rejects.errorsFor.applies_iff_mem error).mp (by simp)
      exact noErrors error applies

end Validates

/-- Every raw workspace is either valid or canonically rejected. -/
theorem validates_or_rejects (raw : RawWorkspace) :
    (∃ workspace, Validates raw workspace) ∨
      ∃ errors, Rejects raw errors := by
  cases execution : validate raw with
  | error errors =>
      exact Or.inr ⟨errors, validate_errors_sound execution⟩
  | ok workspace =>
      exact Or.inl ⟨workspace, validate_sound execution⟩

namespace ValidatedUserWorkspace

private theorem file_eq_of_mem_of_id_eq
    {files : List WorkspaceFile} {first second : WorkspaceFile}
    (unique : (files.map WorkspaceFile.id).Nodup)
    (firstMember : first ∈ files) (secondMember : second ∈ files)
    (idEqual : first.id = second.id) :
    first = second := by
  induction files with
  | nil => simp at firstMember
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.nodup_cons] at unique
      rw [List.mem_cons] at firstMember secondMember
      rcases firstMember with firstEqual | firstTail
      · subst first
        rcases secondMember with secondEqual | secondTail
        · exact secondEqual.symm
        · have secondIdMember : second.id ∈ tail.map WorkspaceFile.id :=
            List.mem_map.mpr ⟨second, secondTail, rfl⟩
          exact False.elim (unique.1 (idEqual ▸ secondIdMember))
      · rcases secondMember with secondEqual | secondTail
        · subst second
          have firstIdMember : first.id ∈ tail.map WorkspaceFile.id :=
            List.mem_map.mpr ⟨first, firstTail, rfl⟩
          exact False.elim (unique.1 (idEqual ▸ firstIdMember))
        · exact inductionHypothesis unique.2 firstTail secondTail

/-- Distinct validated files cannot share a structured source identity. -/
theorem lookupSource_unique (workspace : ValidatedUserWorkspace)
    {first second : WorkspaceFile}
    (firstMember : first ∈ workspace.files)
    (secondMember : second ∈ workspace.files)
    (idEqual : first.id = second.id) :
    first = second :=
  file_eq_of_mem_of_id_eq workspace.fileIdsUnique
    firstMember secondMember idEqual

/-- Lookup succeeds exactly for the unique validated file with that identity. -/
theorem lookupSource_eq_some_iff (workspace : ValidatedUserWorkspace)
    (id : SourceId) (file : WorkspaceFile) :
    workspace.lookupSource id = some file ↔
      file ∈ workspace.files ∧ file.id = id := by
  constructor
  · intro lookup
    unfold lookupSource at lookup
    exact ⟨List.mem_of_find?_eq_some lookup, by
      have found := List.find?_some lookup
      simpa using found⟩
  · rintro ⟨fileMember, fileId⟩
    unfold lookupSource
    have isSome :
        (workspace.files.find? fun candidate =>
          decide (candidate.id = id)).isSome := by
      rw [List.find?_isSome]
      exact ⟨file, fileMember, by simp [fileId]⟩
    cases lookup : workspace.files.find? (fun candidate =>
        decide (candidate.id = id)) with
    | none => simp [lookup] at isSome
    | some found =>
        have foundMember : found ∈ workspace.files :=
          List.mem_of_find?_eq_some lookup
        have foundId : found.id = id := by
          have predicate := List.find?_some lookup
          simpa using predicate
        have foundEqual : found = file :=
          lookupSource_unique workspace foundMember fileMember
            (foundId.trans fileId.symm)
        subst found
        rfl

/-- The validated entry identity always resolves to its unique source file. -/
theorem entry_lookup (workspace : ValidatedUserWorkspace) :
    ∃ file,
      workspace.lookupSource workspace.entry = some file ∧
        file.id = workspace.entry := by
  obtain ⟨file, fileMember, fileId⟩ := workspace.entryPresent
  exact ⟨file,
    (lookupSource_eq_some_iff workspace workspace.entry file).mpr
      ⟨fileMember, fileId⟩,
    fileId⟩

/-- Every successfully looked-up external source has a declared library. -/
theorem external_file_declared (workspace : ValidatedUserWorkspace)
    (name : ExternalLibraryName) (path : CanonicalSourcePath)
    {file : WorkspaceFile}
    (lookup : workspace.lookupSource
      { library := .external name, path } = some file) :
    name ∈ workspace.declaredExternalLibraries := by
  obtain ⟨fileMember, fileId⟩ :=
    (lookupSource_eq_some_iff workspace
      { library := .external name, path } file).mp lookup
  apply workspace.externalFilesDeclared file fileMember name
  simp [fileId]

end ValidatedUserWorkspace

namespace MainFileOf

/-- Main-file decoding preserves exact UTF-8 content bytes. -/
theorem sourceBytes_eq {raw : RawSourceFile} {file : WorkspaceFile}
    (graph : MainFileOf raw file) :
    RawSourceFile.sourceBytes raw = WorkspaceFile.sourceBytes file := by
  rcases graph with ⟨path, pathGraph, rfl⟩
  rfl

end MainFileOf

namespace TaggedExternalFileOf

/-- Tagged external-file decoding preserves exact UTF-8 content bytes. -/
theorem sourceBytes_eq {raw : String × RawSourceFile}
    {file : WorkspaceFile} (graph : TaggedExternalFileOf raw file) :
    RawSourceFile.sourceBytes raw.2 = WorkspaceFile.sourceBytes file := by
  rcases graph with ⟨name, path, nameGraph, pathGraph, rfl⟩
  rfl

end TaggedExternalFileOf

namespace RawWorkspace

private theorem taggedExternalSources_length_aux
    (libraries : List RawExternalLibrary) :
    (libraries.flatMap fun library =>
      library.sources.map fun source => (library.name, source)).length =
      (libraries.map RawExternalLibrary.sourceFiles).sum := by
  induction libraries with
  | nil => rfl
  | cons library tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.map_cons, List.sum_cons]
      rw [inductionHypothesis]
      rfl

/-- Raw source count is the main count plus flattened tagged external count. -/
theorem sourceFiles_eq_flattened (raw : RawWorkspace) :
    raw.sourceFiles =
      raw.mainSources.length + raw.taggedExternalSources.length := by
  unfold sourceFiles
  unfold taggedExternalSources
  rw [taggedExternalSources_length_aux raw.externalLibraries]

private theorem taggedExternalSources_sourceBytes_aux
    (libraries : List RawExternalLibrary) :
    (libraries.flatMap fun library =>
      library.sources.map RawSourceFile.sourceBytes).sum =
      (libraries.map RawExternalLibrary.sourceBytes).sum := by
  induction libraries with
  | nil => rfl
  | cons library tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.sum_append_nat,
        List.map_cons, List.sum_cons]
      rw [inductionHypothesis]
      rfl

/-- Flattening tagged external records preserves their exact byte total. -/
theorem taggedExternalSources_sourceBytes (raw : RawWorkspace) :
    (raw.taggedExternalSources.map fun tagged =>
      RawSourceFile.sourceBytes tagged.2).sum =
        (raw.externalLibraries.map RawExternalLibrary.sourceBytes).sum := by
  unfold taggedExternalSources
  rw [List.map_flatMap]
  simp only [List.map_map]
  exact taggedExternalSources_sourceBytes_aux raw.externalLibraries

/-- Raw byte count splits over main and flattened tagged external records. -/
theorem sourceBytes_eq_flattened (raw : RawWorkspace) :
    raw.sourceBytes =
      (raw.mainSources.map RawSourceFile.sourceBytes).sum +
        (raw.taggedExternalSources.map fun tagged =>
          RawSourceFile.sourceBytes tagged.2).sum := by
  unfold sourceBytes
  rw [taggedExternalSources_sourceBytes]

/-- Raw-workspace equivalence preserves exact source-record count. -/
theorem Equivalent.sourceFiles_eq {left right : RawWorkspace}
    (equivalent : left.Equivalent right) :
    left.sourceFiles = right.sourceFiles := by
  rw [sourceFiles_eq_flattened, sourceFiles_eq_flattened,
    equivalent.mainSources_perm.length_eq,
    equivalent.taggedExternalSources_perm.length_eq]

/-- Raw-workspace equivalence preserves exact UTF-8 source bytes. -/
theorem Equivalent.sourceBytes_eq {left right : RawWorkspace}
    (equivalent : left.Equivalent right) :
    left.sourceBytes = right.sourceBytes := by
  rw [sourceBytes_eq_flattened, sourceBytes_eq_flattened,
    (equivalent.mainSources_perm.map RawSourceFile.sourceBytes).sum_nat,
    (equivalent.taggedExternalSources_perm.map fun tagged =>
      RawSourceFile.sourceBytes tagged.2).sum_nat]

end RawWorkspace

namespace Validates

/-- Declarative validation preserves the exact source-record count. -/
theorem sourceFiles_eq {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (validates : Validates raw workspace) :
    workspace.sourceFiles = raw.sourceFiles := by
  rcases validates with
    ⟨relational, _, _, _, mainGraph, _, externalGraph, _, files⟩
  unfold ValidatedUserWorkspace.sourceFiles
  rw [RawWorkspace.sourceFiles_eq_flattened,
    files.length_eq, List.length_append,
    ListCorresponds.length_eq mainGraph,
    ListCorresponds.length_eq externalGraph]

/-- Declarative validation preserves exact UTF-8 source bytes. -/
theorem sourceBytes_eq {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (validates : Validates raw workspace) :
    workspace.sourceBytes = raw.sourceBytes := by
  rcases validates with
    ⟨relational, _, _, _, mainGraph, _, externalGraph, _, files⟩
  unfold ValidatedUserWorkspace.sourceBytes
  rw [RawWorkspace.sourceBytes_eq_flattened,
    (files.map WorkspaceFile.sourceBytes).sum_nat,
    List.map_append, List.sum_append_nat,
    ListCorresponds.sum_map_eq RawSourceFile.sourceBytes
      WorkspaceFile.sourceBytes MainFileOf.sourceBytes_eq mainGraph,
    ListCorresponds.sum_map_eq
      (fun tagged => RawSourceFile.sourceBytes tagged.2)
      WorkspaceFile.sourceBytes
      TaggedExternalFileOf.sourceBytes_eq externalGraph]

end Validates

/-- Successful executable validation preserves exact source-record count. -/
theorem validate_preserves_sourceFiles {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (accepted : validate raw = .ok workspace) :
    workspace.sourceFiles = raw.sourceFiles :=
  Validates.sourceFiles_eq (validate_sound accepted)

/-- Successful executable validation preserves exact UTF-8 source bytes. -/
theorem validate_preserves_sourceBytes {raw : RawWorkspace}
    {workspace : ValidatedUserWorkspace}
    (accepted : validate raw = .ok workspace) :
    workspace.sourceBytes = raw.sourceBytes :=
  Validates.sourceBytes_eq (validate_sound accepted)

/-- Equivalent raw workspaces have identical executable validation results. -/
theorem validate_equivalent {left right : RawWorkspace}
    (equivalent : left.Equivalent right) :
    validate left = validate right := by
  cases leftResult : validate left with
  | error errors =>
      have leftRejects := validate_errors_sound leftResult
      have rightRejects :=
        (Rejects.equivalent_iff equivalent errors).mp leftRejects
      have rightResult := validate_errors_complete rightRejects
      rw [rightResult]
  | ok workspace =>
      have leftValidates := validate_sound leftResult
      have rightValidates :=
        (Validates.equivalent_iff equivalent workspace).mp leftValidates
      have rightResult := validate_complete rightValidates
      rw [rightResult]

end Solcore.Workspace
