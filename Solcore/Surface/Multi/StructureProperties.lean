import Solcore.Surface.Multi.StructureFuelProperties
import Solcore.Surface.Multi.Structure

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace Structure

/-- A selected occurrence either repeats a key from `seen` or from its prefix. -/
private def SeenLaterDuplicate {α κ : Type}
    (seen : List κ) (key : α → κ) (later : α) : List α → Prop
  | [] => False
  | head :: tail =>
      (head = later ∧ key head ∈ seen) ∨
        SeenLaterDuplicate (key head :: seen) key later tail

private theorem seenLaterDuplicate_iff {α κ : Type}
    {seen : List κ} {key : α → κ} {later : α} {values : List α} :
    SeenLaterDuplicate seen key later values ↔
      (later ∈ values ∧ key later ∈ seen) ∨
        LaterDuplicate values key later := by
  induction values generalizing seen with
  | nil => simp [SeenLaterDuplicate, LaterDuplicate]
  | cons head tail induction =>
      constructor
      · intro selected
        rcases selected with headSelected | tailSelected
        · rcases headSelected with ⟨headEq, keyMember⟩
          subst head
          exact Or.inl ⟨by simp, keyMember⟩
        · rcases (induction (seen := key head :: seen)).mp tailSelected with
            prior | duplicate
          · rcases prior with ⟨member, keyMember⟩
            rcases List.mem_cons.mp keyMember with headKey | seenKey
            · apply Or.inr
              exact LaterDuplicate.of_head member rfl headKey.symm
            · exact Or.inl ⟨List.mem_cons_of_mem head member, seenKey⟩
          · exact Or.inr (LaterDuplicate.of_tail duplicate)
      · intro selected
        rcases selected with prior | duplicate
        · rcases prior with ⟨member, keyMember⟩
          rcases List.mem_cons.mp member with headEq | tailMember
          · subst head
            exact Or.inl ⟨rfl, keyMember⟩
          · apply Or.inr
            apply (induction (seen := key head :: seen)).mpr
            exact Or.inl ⟨tailMember,
              List.mem_cons_of_mem (key head) keyMember⟩
        · rcases (laterDuplicate_cons_iff head tail key later).mp duplicate with
            tailDuplicate | headDuplicate
          · apply Or.inr
            exact (induction (seen := key head :: seen)).mpr
              (Or.inr tailDuplicate)
          · rcases headDuplicate with
              ⟨candidate, member, candidateEq, keyEq⟩
            subst candidate
            apply Or.inr
            apply (induction (seen := key head :: seen)).mpr
            exact Or.inl ⟨member, List.mem_cons.mpr (Or.inl keyEq.symm)⟩

private theorem mem_duplicateDiagnostics_go_iff {α κ : Type}
    [DecidableEq κ]
    {seen : List κ} {key : α → κ}
    {makeDiagnostic : α → StructuralDiagnostic}
    {values : List α} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈
        duplicateDiagnostics.go key makeDiagnostic seen values ↔
      ∃ value,
        SeenLaterDuplicate seen key value values ∧
          makeDiagnostic value = diagnostic := by
  induction values generalizing seen with
  | nil => simp [duplicateDiagnostics.go, SeenLaterDuplicate]
  | cons head tail induction =>
      by_cases repeated : key head ∈ seen
      · rw [duplicateDiagnostics.go.eq_2, if_pos repeated]
        constructor
        · intro member
          rcases List.mem_cons.mp member with headMember | tailMember
          · exact ⟨head, Or.inl ⟨rfl, repeated⟩, headMember.symm⟩
          · rcases (induction (seen := key head :: seen)).mp tailMember with
              ⟨value, selected, equality⟩
            exact ⟨value, Or.inr selected, equality⟩
        · rintro ⟨value, selected, equality⟩
          rcases selected with headSelected | tailSelected
          · rcases headSelected with ⟨headEq, _⟩
            subst value
            exact List.mem_cons.mpr (Or.inl equality.symm)
          · apply List.mem_cons.mpr
            apply Or.inr
            exact (induction (seen := key head :: seen)).mpr
              ⟨value, tailSelected, equality⟩
      · rw [duplicateDiagnostics.go.eq_2, if_neg repeated]
        constructor
        · intro tailMember
          rcases (induction (seen := key head :: seen)).mp tailMember with
            ⟨value, selected, equality⟩
          exact ⟨value, Or.inr selected, equality⟩
        · rintro ⟨value, selected, equality⟩
          rcases selected with headSelected | tailSelected
          · exact False.elim (repeated headSelected.2)
          · exact (induction (seen := key head :: seen)).mpr
              ⟨value, tailSelected, equality⟩

/-- The duplicate collector emits exactly diagnostics for later equal keys. -/
theorem mem_duplicateDiagnostics_iff_laterDuplicate {α κ : Type}
    [DecidableEq κ]
    {key : α → κ} {makeDiagnostic : α → StructuralDiagnostic}
    {values : List α} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ duplicateDiagnostics key makeDiagnostic values ↔
      ∃ value,
        LaterDuplicate values key value ∧
          makeDiagnostic value = diagnostic := by
  change diagnostic ∈
      duplicateDiagnostics.go key makeDiagnostic [] values ↔ _
  rw [mem_duplicateDiagnostics_go_iff]
  constructor
  · rintro ⟨value, selected, equality⟩
    have duplicate : LaterDuplicate values key value := by
      rcases (seenLaterDuplicate_iff.mp selected) with prior | duplicate
      · simp at prior
      · exact duplicate
    exact ⟨value, duplicate, equality⟩
  · rintro ⟨value, duplicate, equality⟩
    exact ⟨value, seenLaterDuplicate_iff.mpr (Or.inr duplicate), equality⟩

/-- The executable span comparison is the independent strict span order. -/
@[simp] theorem sourceSpanBefore_eq_true_iff
    (left right : SourceSpan) :
    sourceSpanBefore left right = true ↔ SpanBefore left right := by
  cases ordering : SourceId.compare left.source right.source with
  | lt => simp [sourceSpanBefore, SpanBefore, ordering]
  | eq =>
      have sourceEq : left.source = right.source :=
        SourceId.compare_eq_iff_eq.mp ordering
      have selfOrdering :
          SourceId.compare right.source right.source = .eq :=
        Std.ReflCmp.compare_self
      simp [sourceSpanBefore, SpanBefore, sourceEq, selfOrdering]
      by_cases startBefore : left.startByte < right.startByte
      · simp [startBefore]
      · have rightLeLeft : right.startByte ≤ left.startByte :=
          Nat.le_of_not_gt startBefore
        simp only [startBefore, false_or]
        constructor
        · rintro ⟨leftLeRight, endBefore⟩
          exact ⟨Nat.le_antisymm leftLeRight rightLeLeft, endBefore⟩
        · rintro ⟨startEq, endBefore⟩
          exact ⟨Nat.le_of_eq startEq, endBefore⟩
  | gt =>
      have sourceNe : left.source ≠ right.source := by
        intro sourceEq
        have equalOrdering :
            SourceId.compare left.source right.source = .eq :=
          SourceId.compare_eq_iff_eq.mpr sourceEq
        rw [ordering] at equalOrdering
        contradiction
      simp [sourceSpanBefore, SpanBefore, ordering, sourceNe]

private theorem span_eq_of_not_before_not_before
    {left right : SourceSpan}
    (notForward : ¬SpanBefore left right)
    (notBackward : ¬SpanBefore right left) :
    left = right := by
  have sourceEq : left.source = right.source := by
    cases ordering : SourceId.compare left.source right.source with
    | lt => exact False.elim (notForward (SpanBefore.of_source ordering))
    | eq => exact SourceId.compare_eq_iff_eq.mp ordering
    | gt =>
        have reverse : SourceId.compare right.source left.source = .lt :=
          Std.OrientedCmp.lt_of_gt (cmp := SourceId.compare) ordering
        exact False.elim (notBackward (SpanBefore.of_source reverse))
  have startEq : left.startByte = right.startByte := by
    rcases Nat.lt_trichotomy left.startByte right.startByte with
        forward | equal | backward
    · exact False.elim
        (notForward (SpanBefore.of_start sourceEq forward))
    · exact equal
    · exact False.elim
        (notBackward (SpanBefore.of_start sourceEq.symm backward))
  have endEq : left.endByte = right.endByte := by
    rcases Nat.lt_trichotomy left.endByte right.endByte with
        forward | equal | backward
    · exact False.elim
        (notForward (SpanBefore.of_end sourceEq startEq forward))
    · exact equal
    · exact False.elim
        (notBackward
          (SpanBefore.of_end sourceEq.symm startEq.symm backward))
  cases left
  cases right
  simp_all

private theorem leastSpanIn_unique
    {left right : SourceSpan} {spans : List SourceSpan}
    (leftLeast : LeastSpanIn left spans)
    (rightLeast : LeastSpanIn right spans) :
    left = right := by
  apply span_eq_of_not_before_not_before
  · exact rightLeast.not_before leftLeast.member
  · exact leftLeast.not_before rightLeast.member

private def leastSourceSpanStep
    (least candidate : SourceSpan) : SourceSpan :=
  if sourceSpanBefore candidate least then candidate else least

private theorem leastSpanIn_append_step
    {least : SourceSpan} {spans : List SourceSpan}
    (leastProof : LeastSpanIn least spans)
    (candidate : SourceSpan) :
    LeastSpanIn (leastSourceSpanStep least candidate)
      (spans ++ [candidate]) := by
  by_cases candidateBefore : sourceSpanBefore candidate least = true
  · have candidateBeforeProof : SpanBefore candidate least :=
      (sourceSpanBefore_eq_true_iff candidate least).mp candidateBefore
    simp only [leastSourceSpanStep, candidateBefore, if_true]
    constructor
    · simp
    · rw [noSpanBefore_iff]
      intro current member currentBefore
      rcases List.mem_append.mp member with oldMember | candidateMember
      · exact leastProof.not_before oldMember
          (SpanBefore.trans currentBefore candidateBeforeProof)
      · have currentEq : current = candidate := by
          simpa using candidateMember
        subst current
        exact spanBefore_self candidate currentBefore
  · have candidateNotBefore : ¬SpanBefore candidate least := by
      intro beforeProof
      exact candidateBefore
        ((sourceSpanBefore_eq_true_iff candidate least).mpr beforeProof)
    simp only [leastSourceSpanStep, candidateBefore]
    constructor
    · exact List.mem_append.mpr (Or.inl leastProof.member)
    · rw [noSpanBefore_iff]
      intro current member
      rcases List.mem_append.mp member with oldMember | candidateMember
      · exact leastProof.not_before oldMember
      · have currentEq : current = candidate := by
          simpa using candidateMember
        subst current
        exact candidateNotBefore

private theorem foldl_leastSourceSpanStep
    {least : SourceSpan} {spans : List SourceSpan}
    (leastProof : LeastSpanIn least spans)
    (remaining : List SourceSpan) :
    LeastSpanIn (remaining.foldl leastSourceSpanStep least)
      (spans ++ remaining) := by
  induction remaining generalizing least spans with
  | nil => simpa using leastProof
  | cons candidate rest induction =>
      simp only [List.foldl_cons]
      have nextLeast := leastSpanIn_append_step leastProof candidate
      have finalLeast := induction nextLeast
      simpa [List.append_assoc] using finalLeast

/-- The executable fold returns exactly the declaratively least listed span. -/
theorem leastSourceSpan?_eq_some_iff
    {spans : List SourceSpan} {span : SourceSpan} :
    leastSourceSpan? spans = some span ↔ LeastSpanIn span spans := by
  cases spans with
  | nil => simp [leastSourceSpan?, LeastSpanIn]
  | cons first rest =>
      have firstLeast : LeastSpanIn first [first] :=
        leastSpanIn_singleton first
      have computedLeast :
          LeastSpanIn (rest.foldl leastSourceSpanStep first)
            (first :: rest) := by
        have folded := foldl_leastSourceSpanStep firstLeast rest
        simpa using folded
      change some (rest.foldl leastSourceSpanStep first) = some span ↔ _
      constructor
      · intro selected
        have selectedEq : rest.foldl leastSourceSpanStep first = span :=
          Option.some.inj selected
        simpa [selectedEq] using computedLeast
      · intro spanLeast
        exact congrArg some (leastSpanIn_unique computedLeast spanLeast)

/-- The executable wildcard projection is the declarative import projection. -/
@[simp] theorem filterMap_importWildcardSpan?_eq_importWildcardSpans
    (entries : List ImportSelectorEntry) :
    entries.filterMap importWildcardSpan? =
      StructuralDiagnostic.importWildcardSpans entries := by
  rfl

/-- The executable named-import projection is its declarative counterpart. -/
@[simp] theorem namedImportEntries_eq_namedImportBindings
    (entries : List ImportSelectorEntry) :
    namedImportEntries entries =
      StructuralDiagnostic.namedImportBindings entries := by
  rfl

/-- A mixed-wildcard collector emits exactly the least written wildcard when
the surrounding selector has more or fewer than one entry. -/
theorem mem_mixedWildcardDiagnostic?_iff
    {entryCount : Nat} {spans : List SourceSpan}
    {makeDiagnostic : SourceSpan → StructuralDiagnostic}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ mixedWildcardDiagnostic? entryCount spans makeDiagnostic ↔
      entryCount ≠ 1 ∧ ∃ span,
        LeastSpanIn span spans ∧ makeDiagnostic span = diagnostic := by
  unfold mixedWildcardDiagnostic?
  by_cases countOne : entryCount = 1
  · simp [countOne]
  · simp only [countOne, if_false]
    cases selected : leastSourceSpan? spans with
    | none =>
        simp only [List.not_mem_nil, false_iff, not_and, not_exists]
        intro _ span least
        have emitted := leastSourceSpan?_eq_some_iff.mpr least
        rw [selected] at emitted
        contradiction
    | some span =>
        simp only [List.mem_singleton]
        have spanLeast := leastSourceSpan?_eq_some_iff.mp selected
        constructor
        · intro equality
          exact ⟨countOne, span, spanLeast, equality.symm⟩
        · rintro ⟨_, candidate, least, equality⟩
          have candidateSelected := leastSourceSpan?_eq_some_iff.mpr least
          rw [selected] at candidateSelected
          have candidateEq := Option.some.inj candidateSelected
          subst candidate
          exact equality.symm

/-- The import-selection collector emits exactly the four local diagnostics
described by the independent judgment. -/
theorem mem_importSelectionDiagnostics_iff
    {selection : ImportSelection}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ importSelectionDiagnostics selection ↔
      (selection.payload.entries = [] ∧
        diagnostic = .emptyImportSelection selection.span) ∨
      (selection.payload.entries.length ≠ 1 ∧
        ∃ span,
          LeastSpanIn span
            (StructuralDiagnostic.importWildcardSpans
              selection.payload.entries) ∧
          StructuralDiagnostic.mixedImportWildcard span = diagnostic) ∨
      (∃ binding,
        LaterDuplicate
          (StructuralDiagnostic.namedImportBindings
            selection.payload.entries)
          (fun value => value.1.payload) binding ∧
        StructuralDiagnostic.duplicateImportSourceName
          binding.1.span binding.1.payload = diagnostic) ∨
      ∃ binding,
        LaterDuplicate
          (StructuralDiagnostic.namedImportBindings
            selection.payload.entries)
          (fun value => value.2.payload) binding ∧
        StructuralDiagnostic.duplicateImportLocalName
          binding.2.span binding.2.payload = diagnostic := by
  simp [importSelectionDiagnostics, mem_mixedWildcardDiagnostic?_iff,
    mem_duplicateDiagnostics_iff_laterDuplicate]

/-- The hiding-clause collector emits exactly its empty-list and later-key
duplicate diagnostics. -/
theorem mem_hidingDiagnostics_iff
    {clause : HidingClause} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ hidingDiagnostics clause ↔
      (clause.payload.names = [] ∧
        diagnostic = .emptyHidingClause clause.span) ∨
      ∃ name,
        LaterDuplicate clause.payload.names
          (fun value => value.payload) name ∧
        StructuralDiagnostic.duplicateHiddenName
          name.span name.payload = diagnostic := by
  simp [hidingDiagnostics, mem_duplicateDiagnostics_iff_laterDuplicate]

/-- Every diagnostic emitted for a reached import selection is declaratively
applicable. -/
theorem mem_importSelectionDiagnostics_applies
    {module : ParsedModuleV1} {selection : ImportSelection}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.importSelection selection))
    (member : diagnostic ∈ importSelectionDiagnostics selection) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_importSelectionDiagnostics_iff] at member
  rcases member with empty | mixed | sourceDuplicate | localDuplicate
  · rcases empty with ⟨entries, diagnosticEq⟩
    subst diagnostic
    exact .emptyImportSelection occurrence entries
  · rcases mixed with ⟨entryCount, span, least, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .mixedImportWildcard occurrence entryCount least
  · rcases sourceDuplicate with ⟨binding, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicateImportSourceName occurrence later
  · rcases localDuplicate with ⟨binding, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicateImportLocalName occurrence later

/-- Every diagnostic emitted for a reached hiding clause is declaratively
applicable. -/
theorem mem_hidingDiagnostics_applies
    {module : ParsedModuleV1} {clause : HidingClause}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.hidingClause clause))
    (member : diagnostic ∈ hidingDiagnostics clause) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_hidingDiagnostics_iff] at member
  rcases member with empty | duplicate
  · rcases empty with ⟨names, diagnosticEq⟩
    subst diagnostic
    exact .emptyHidingClause occurrence names
  · rcases duplicate with ⟨name, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicateHiddenName occurrence later

/-- Every diagnostic emitted for a top-level import declaration is
declaratively applicable to the containing module. -/
theorem mem_importDiagnostics_applies
    {module : ParsedModuleV1} {item : TopItem}
    {declaration : ImportDecl} {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (itemShape : item.payload = .importDecl declaration)
    (member : diagnostic ∈ importDiagnostics declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases modeShape : declaration.payload.mode with
  | module alias =>
      simp [importDiagnostics, modeShape] at member
  | items selection hidingClause =>
      rw [importDiagnostics, modeShape, List.mem_append] at member
      rcases member with selectionMember | hidingMember
      · exact mem_importSelectionDiagnostics_applies
          (.importSelectionTop itemMember itemShape modeShape)
          selectionMember
      · cases hidingClause with
        | none => simp at hidingMember
        | some clause =>
            exact mem_hidingDiagnostics_applies
              (.hidingClauseTop itemMember itemShape modeShape)
              hidingMember

/-- Constructor-selection diagnostics are exactly later duplicate constructor
names from a written named selection. -/
theorem mem_constructorSelectionDiagnostics_iff
    {selected : Option ConstructorSelection}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ constructorSelectionDiagnostics selected ↔
      ∃ selection constructors name,
        selected = some selection ∧
        selection.payload = .named constructors ∧
        LaterDuplicate constructors.toList
          (fun value => value.payload) name ∧
        StructuralDiagnostic.duplicateExportConstructor
          name.span name.payload = diagnostic := by
  cases selected with
  | none => simp [constructorSelectionDiagnostics]
  | some selection =>
      cases shape : selection.payload with
      | all marker => simp [constructorSelectionDiagnostics, shape]
      | named constructors =>
          simp [constructorSelectionDiagnostics, shape,
            mem_duplicateDiagnostics_iff_laterDuplicate,
            nonemptyToList, NonemptyList.toList]

/-- Export-item diagnostics are exactly later duplicate constructor names in
that item's named constructor selection. -/
theorem mem_exportItemDiagnostics_iff
    {item : ExportItem} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ exportItemDiagnostics item ↔
      ∃ selection constructors name,
        item.payload.constructors = some selection ∧
        selection.payload = .named constructors ∧
        LaterDuplicate constructors.toList
          (fun value => value.payload) name ∧
        StructuralDiagnostic.duplicateExportConstructor
          name.span name.payload = diagnostic := by
  simpa [exportItemDiagnostics] using
    (mem_constructorSelectionDiagnostics_iff
      (selected := item.payload.constructors)
      (diagnostic := diagnostic))

/-- Membership in the local-item projection retains an original export entry
witness. -/
theorem mem_localExportItems_iff_entry
    {entries : List ExportEntry} {item : ExportItem} :
    item ∈ StructuralDiagnostic.localExportItems entries ↔
      ∃ entry, entry ∈ entries ∧ entry.payload = .item item := by
  rw [StructuralDiagnostic.localExportItems, List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, selected⟩
    cases shape : entry.payload with
    | wildcard marker => simp [shape] at selected
    | item candidate =>
        simp only [shape, Option.some.injEq] at selected
        subst candidate
        exact ⟨entry, member, shape⟩
    | allFrom reference marker => simp [shape] at selected
  · rintro ⟨entry, member, shape⟩
    exact ⟨entry, member, by simp [shape]⟩

/-- Membership in the remote-item projection retains an original braced entry
witness. -/
theorem mem_remoteExportItems_iff_entry
    {entries : List RemoteExportEntry} {item : ExportItem} :
    item ∈ StructuralDiagnostic.remoteExportItems entries ↔
      ∃ entry, entry ∈ entries ∧ entry.payload = .item item := by
  rw [StructuralDiagnostic.remoteExportItems, List.mem_filterMap]
  constructor
  · rintro ⟨entry, member, selected⟩
    cases shape : entry.payload with
    | wildcard marker => simp [shape] at selected
    | item candidate =>
        simp only [shape, Option.some.injEq] at selected
        subst candidate
        exact ⟨entry, member, shape⟩
  · rintro ⟨entry, member, shape⟩
    exact ⟨entry, member, by simp [shape]⟩

private theorem localExportDiagnostics_expansion
    (selection : LocalExportList) :
    localExportDiagnostics selection =
      let entries := selection.payload.entries
      let items := StructuralDiagnostic.localExportItems entries
      let references := StructuralDiagnostic.localExportReferences entries
      let empty :=
        if entries.isEmpty then
          [.emptyLocalExportList selection.span]
        else []
      let mixed := mixedWildcardDiagnostic? entries.length
        (StructuralDiagnostic.localExportWildcardSpans entries)
        StructuralDiagnostic.mixedExportWildcard
      let duplicateNames := duplicateDiagnostics
        (fun item => item.payload.name.payload)
        (fun item => .duplicateExportName
          item.payload.name.span item.payload.name.payload)
        items
      let duplicateReferences := duplicateDiagnostics
        ModuleReference.eraseLocations
        (fun reference => .duplicateExportModuleReference
          reference.span reference.eraseLocations)
        references
      empty ++ mixed ++ duplicateNames ++ duplicateReferences ++
        items.flatMap exportItemDiagnostics := by
  rfl

/-- The local-export collector emits exactly its four selection diagnostics
and the constructor diagnostics of projected export items. -/
theorem mem_localExportDiagnostics_iff
    {selection : LocalExportList} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ localExportDiagnostics selection ↔
      (selection.payload.entries = [] ∧
        diagnostic = .emptyLocalExportList selection.span) ∨
      (selection.payload.entries.length ≠ 1 ∧
        ∃ span,
          LeastSpanIn span
            (StructuralDiagnostic.localExportWildcardSpans
              selection.payload.entries) ∧
          StructuralDiagnostic.mixedExportWildcard span = diagnostic) ∨
      (∃ item,
        LaterDuplicate
          (StructuralDiagnostic.localExportItems
            selection.payload.entries)
          (fun value => value.payload.name.payload) item ∧
        StructuralDiagnostic.duplicateExportName
          item.payload.name.span item.payload.name.payload = diagnostic) ∨
      (∃ reference,
        LaterDuplicate
          (StructuralDiagnostic.localExportReferences
            selection.payload.entries)
          ModuleReference.eraseLocations reference ∧
        StructuralDiagnostic.duplicateExportModuleReference
          reference.span reference.eraseLocations = diagnostic) ∨
      ∃ item,
        item ∈ StructuralDiagnostic.localExportItems
          selection.payload.entries ∧
        diagnostic ∈ exportItemDiagnostics item := by
  rw [localExportDiagnostics_expansion]
  simp [mem_mixedWildcardDiagnostic?_iff,
    mem_duplicateDiagnostics_iff_laterDuplicate]

private theorem remoteExportDiagnostics_expansion
    (selection : RemoteExportSelection)
    (entries : List RemoteExportEntry)
    (braced : selection.payload = .braced entries) :
    remoteExportDiagnostics selection =
      let items := StructuralDiagnostic.remoteExportItems entries
      let empty :=
        if entries.isEmpty then
          [.emptyRemoteExportList selection.span]
        else []
      let mixed := mixedWildcardDiagnostic? entries.length
        (StructuralDiagnostic.remoteExportWildcardSpans entries)
        StructuralDiagnostic.mixedExportWildcard
      let duplicateNames := duplicateDiagnostics
        (fun item => item.payload.name.payload)
        (fun item => .duplicateExportName
          item.payload.name.span item.payload.name.payload)
        items
      empty ++ mixed ++ duplicateNames ++
        items.flatMap exportItemDiagnostics := by
  rw [remoteExportDiagnostics, braced]
  rfl

/-- A braced remote-export collector emits exactly its three selection
diagnostics and the constructor diagnostics of projected export items. -/
theorem mem_remoteExportDiagnostics_braced_iff
    {selection : RemoteExportSelection}
    {entries : List RemoteExportEntry}
    {diagnostic : StructuralDiagnostic}
    (braced : selection.payload = .braced entries) :
    diagnostic ∈ remoteExportDiagnostics selection ↔
      (entries = [] ∧
        diagnostic = .emptyRemoteExportList selection.span) ∨
      (entries.length ≠ 1 ∧
        ∃ span,
          LeastSpanIn span
            (StructuralDiagnostic.remoteExportWildcardSpans entries) ∧
          StructuralDiagnostic.mixedExportWildcard span = diagnostic) ∨
      (∃ item,
        LaterDuplicate
          (StructuralDiagnostic.remoteExportItems entries)
          (fun value => value.payload.name.payload) item ∧
        StructuralDiagnostic.duplicateExportName
          item.payload.name.span item.payload.name.payload = diagnostic) ∨
      ∃ item,
        item ∈ StructuralDiagnostic.remoteExportItems entries ∧
        diagnostic ∈ exportItemDiagnostics item := by
  rw [remoteExportDiagnostics_expansion selection entries braced]
  simp [mem_mixedWildcardDiagnostic?_iff,
    mem_duplicateDiagnostics_iff_laterDuplicate]

/-- Every diagnostic emitted for a reached export item is declaratively
applicable. -/
theorem mem_exportItemDiagnostics_applies
    {module : ParsedModuleV1} {item : ExportItem}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.exportItem item))
    (member : diagnostic ∈ exportItemDiagnostics item) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_exportItemDiagnostics_iff] at member
  rcases member with
    ⟨selection, constructors, name, selected, named, later, diagnosticEq⟩
  rw [← diagnosticEq]
  exact .duplicateExportConstructor occurrence selected named later

/-- Every diagnostic emitted for a reached local export list is declaratively
applicable. -/
theorem mem_localExportDiagnostics_applies
    {module : ParsedModuleV1} {selection : LocalExportList}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.localExportList selection))
    (member : diagnostic ∈ localExportDiagnostics selection) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_localExportDiagnostics_iff] at member
  rcases member with empty | mixed | duplicateName |
      duplicateReference | nested
  · rcases empty with ⟨entries, diagnosticEq⟩
    subst diagnostic
    exact .emptyLocalExportList occurrence entries
  · rcases mixed with ⟨entryCount, span, least, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .mixedLocalExportWildcard occurrence entryCount least
  · rcases duplicateName with ⟨item, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicateLocalExportName occurrence later
  · rcases duplicateReference with
      ⟨reference, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicateExportModuleReference occurrence later
  · rcases nested with ⟨item, itemMember, diagnosticMember⟩
    rcases mem_localExportItems_iff_entry.mp itemMember with
      ⟨entry, entryMember, entryShape⟩
    exact mem_exportItemDiagnostics_applies
      (.localExportItem occurrence entryMember entryShape)
      diagnosticMember

/-- Every diagnostic emitted for a reached remote export selection is
declaratively applicable. -/
theorem mem_remoteExportDiagnostics_applies
    {module : ParsedModuleV1} {selection : RemoteExportSelection}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.remoteExportSelection selection))
    (member : diagnostic ∈ remoteExportDiagnostics selection) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases shape : selection.payload with
  | dotWildcard marker =>
      simp [remoteExportDiagnostics, shape] at member
  | braced entries =>
      rw [mem_remoteExportDiagnostics_braced_iff shape] at member
      rcases member with empty | mixed | duplicateName | nested
      · rcases empty with ⟨entriesEmpty, diagnosticEq⟩
        subst diagnostic
        exact .emptyRemoteExportList entries occurrence shape entriesEmpty
      · rcases mixed with ⟨entryCount, span, least, diagnosticEq⟩
        rw [← diagnosticEq]
        exact .mixedRemoteExportWildcard occurrence shape entryCount least
      · rcases duplicateName with ⟨item, later, diagnosticEq⟩
        rw [← diagnosticEq]
        exact .duplicateRemoteExportName occurrence shape later
      · rcases nested with ⟨item, itemMember, diagnosticMember⟩
        rcases mem_remoteExportItems_iff_entry.mp itemMember with
          ⟨entry, entryMember, entryShape⟩
        exact mem_exportItemDiagnostics_applies
          (.remoteExportItem occurrence shape entryMember entryShape)
          diagnosticMember

/-- Every diagnostic emitted for a top-level export declaration is
declaratively applicable to the containing module. -/
theorem mem_exportDiagnostics_applies
    {module : ParsedModuleV1} {item : TopItem}
    {declaration : ExportDecl} {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (itemShape : item.payload = .exportDecl declaration)
    (member : diagnostic ∈ exportDiagnostics declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases modeShape : declaration.payload with
  | module moduleReference alias =>
      simp [exportDiagnostics, modeShape] at member
  | «local» selection =>
      rw [exportDiagnostics, modeShape] at member
      exact mem_localExportDiagnostics_applies
        (.localExportListTop itemMember itemShape modeShape) member
  | «from» moduleReference selection =>
      rw [exportDiagnostics, modeShape] at member
      exact mem_remoteExportDiagnostics_applies
        (.remoteExportSelectionTop itemMember itemShape modeShape) member

/-- Missing-parameter diagnostics retain the original parameter occurrence
and exactly characterize an absent required type annotation. -/
theorem mem_missingParameterTypeDiagnostics_iff
    {context : ParameterContext} {parameters : List Parameter}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ missingParameterTypeDiagnostics context parameters ↔
      ∃ parameter,
        parameter ∈ parameters ∧
        parameter.payload.type = none ∧
        StructuralDiagnostic.requiredParameterTypeMissing
          parameter.payload.name.span context = diagnostic := by
  rw [missingParameterTypeDiagnostics, List.mem_filterMap]
  constructor
  · rintro ⟨parameter, member, selected⟩
    cases typeShape : parameter.payload.type with
    | none =>
        simp only [typeShape, Option.some.injEq] at selected
        exact ⟨parameter, member, typeShape, selected⟩
    | some typeExpression => simp [typeShape] at selected
  · rintro ⟨parameter, member, missing, diagnosticEq⟩
    exact ⟨parameter, member, by simp [missing, diagnosticEq]⟩

/-- Disallowed-signature diagnostics are exactly the selected public or
payable modifier markers, including when both positions yield one value. -/
theorem mem_disallowedSignatureModifierDiagnostics_iff
    {context : ModifierContext} {signature : FunctionSignature}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈
        disallowedSignatureModifierDiagnostics context signature ↔
      (∃ marker,
        signature.payload.public = some marker ∧
        StructuralDiagnostic.modifierNotAllowed
          marker.span context marker.payload = diagnostic) ∨
      ∃ marker,
        signature.payload.payable = some marker ∧
        StructuralDiagnostic.modifierNotAllowed
          marker.span context marker.payload = diagnostic := by
  cases publicShape : signature.payload.public <;>
    cases payableShape : signature.payload.payable <;>
      simp [disallowedSignatureModifierDiagnostics, publicShape,
        payableShape, eq_comm]

/-- Every missing-parameter diagnostic emitted for a reached signature is
declaratively applicable. -/
theorem mem_missingParameterTypeDiagnostics_applies
    {module : ParsedModuleV1}
    {modifierContext : Option ModifierContext}
    {parameterContext : ParameterContext}
    {signature : FunctionSignature}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.signature modifierContext parameterContext signature))
    (member : diagnostic ∈ missingParameterTypeDiagnostics
      parameterContext signature.payload.parameters) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_missingParameterTypeDiagnostics_iff] at member
  rcases member with ⟨parameter, parameterMember, missing, diagnosticEq⟩
  rw [← diagnosticEq]
  exact .signatureParameterTypeMissing occurrence parameterMember missing

/-- Every disallowed modifier emitted for a reached restricted signature is
declaratively applicable. -/
theorem mem_disallowedSignatureModifierDiagnostics_applies
    {module : ParsedModuleV1} {context : ModifierContext}
    {parameterContext : ParameterContext}
    {signature : FunctionSignature}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.signature (some context) parameterContext signature))
    (member : diagnostic ∈
      disallowedSignatureModifierDiagnostics context signature) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_disallowedSignatureModifierDiagnostics_iff] at member
  rcases member with publicSelected | payableSelected
  · rcases publicSelected with ⟨marker, selected, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .signatureModifierNotAllowed occurrence (.publicMarker selected)
  · rcases payableSelected with ⟨marker, selected, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .signatureModifierNotAllowed occurrence (.payableMarker selected)

/-- The pragma collector emits exactly its empty-target and later-duplicate
diagnostics. -/
theorem mem_pragmaDiagnostics_iff
    {declaration : PragmaDecl} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ pragmaDiagnostics declaration ↔
      (declaration.payload.kind.payload = .noGenericInstanceFor ∧
        declaration.payload.targets = [] ∧
        diagnostic = .emptyGenericPragmaTargets
          declaration.payload.kind.span) ∨
      ∃ target,
        LaterDuplicate declaration.payload.targets
          (fun value => value.payload) target ∧
        StructuralDiagnostic.duplicatePragmaTarget
          target.span target.payload = diagnostic := by
  simp [pragmaDiagnostics, mem_duplicateDiagnostics_iff_laterDuplicate,
    and_assoc]

/-- Every diagnostic emitted for a reached pragma is declaratively
applicable. -/
theorem mem_pragmaDiagnostics_applies
    {module : ParsedModuleV1} {declaration : PragmaDecl}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.pragma declaration))
    (member : diagnostic ∈ pragmaDiagnostics declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_pragmaDiagnostics_iff] at member
  rcases member with empty | duplicate
  · rcases empty with ⟨kind, targets, diagnosticEq⟩
    subst diagnostic
    exact .emptyGenericPragmaTargets occurrence kind targets
  · rcases duplicate with ⟨target, later, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .duplicatePragmaTarget occurrence later

/-- Every diagnostic emitted for a top-level pragma is declaratively
applicable to the containing module. -/
theorem mem_pragmaDiagnostics_top_applies
    {module : ParsedModuleV1} {item : TopItem}
    {declaration : PragmaDecl} {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (itemShape : item.payload = .pragmaDecl declaration)
    (member : diagnostic ∈ pragmaDiagnostics declaration) :
    StructuralDiagnostic.Applies module diagnostic :=
  mem_pragmaDiagnostics_applies
    (.pragmaTop itemMember itemShape) member

private structure RecursiveDiagnosticsFuelStep (fuel : Nat) : Prop where
  expression :
    ∀ {expression : Expression} {diagnostic : StructuralDiagnostic},
      diagnostic ∈ expressionDiagnosticsFuel fuel expression →
      diagnostic ∈ expressionDiagnosticsFuel (fuel + 1) expression
  pattern :
    ∀ {pattern : Pattern} {diagnostic : StructuralDiagnostic},
      diagnostic ∈ patternDiagnosticsFuel fuel pattern →
      diagnostic ∈ patternDiagnosticsFuel (fuel + 1) pattern
  body :
    ∀ {loopDepth : Nat} {body : Body}
      {diagnostic : StructuralDiagnostic},
      diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body →
      diagnostic ∈ bodyDiagnosticsFuel (fuel + 1) loopDepth body
  statement :
    ∀ {loopDepth : Nat} {statement : Statement}
      {diagnostic : StructuralDiagnostic},
      diagnostic ∈ statementDiagnosticsFuel fuel loopDepth statement →
      diagnostic ∈ statementDiagnosticsFuel (fuel + 1) loopDepth statement
  forInit :
    ∀ {item : ForInitItem} {diagnostic : StructuralDiagnostic},
      diagnostic ∈ forInitDiagnosticsFuel fuel item →
      diagnostic ∈ forInitDiagnosticsFuel (fuel + 1) item
  forPost :
    ∀ {item : ForPostItem} {diagnostic : StructuralDiagnostic},
      diagnostic ∈ forPostDiagnosticsFuel fuel item →
      diagnostic ∈ forPostDiagnosticsFuel (fuel + 1) item

private theorem recursiveDiagnosticsFuel_step
    (fuel : Nat) : RecursiveDiagnosticsFuelStep fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> simp_all [expressionDiagnosticsFuel,
        patternDiagnosticsFuel, bodyDiagnosticsFuel,
        statementDiagnosticsFuel, forInitDiagnosticsFuel,
        forPostDiagnosticsFuel]
  | succ fuel previous =>
      constructor
      · intro expression diagnostic member
        cases shape : expression.payload with
        | name name => simp [expressionDiagnosticsFuel, shape] at member
        | call callee arguments =>
            simp only [expressionDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with calleeMember | argumentMember
            · exact Or.inl (previous.expression calleeMember)
            · apply Or.inr
              rw [List.mem_flatMap] at argumentMember ⊢
              rcases argumentMember with
                ⟨argument, argumentIn, diagnosticIn⟩
              exact ⟨argument, argumentIn,
                previous.expression diagnosticIn⟩
        | select receiver field =>
            rw [expressionDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
        | dotConstructor marker name arguments =>
            cases arguments with
            | none => simp [expressionDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [expressionDiagnosticsFuel, shape,
                  List.mem_flatMap] at member ⊢
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact ⟨argument, argumentIn,
                  previous.expression diagnosticIn⟩
        | proxy marker typeExpression =>
            simp [expressionDiagnosticsFuel, shape] at member
        | literal literal =>
            simp [expressionDiagnosticsFuel, shape] at member
        | lambda parameters returnType body =>
            rw [expressionDiagnosticsFuel, shape] at member ⊢
            exact previous.body member
        | annotation inner typeExpression =>
            rw [expressionDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
        | keywordConditional condition thenBranch elseBranch =>
            simp only [expressionDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with earlierMember | elseMember
            · rcases earlierMember with conditionMember | thenMember
              · exact Or.inl (Or.inl
                  (previous.expression conditionMember))
              · exact Or.inl (Or.inr
                  (previous.expression thenMember))
            · exact Or.inr (previous.expression elseMember)
        | ternaryConditional condition thenBranch elseBranch =>
            simp only [expressionDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with earlierMember | elseMember
            · rcases earlierMember with conditionMember | thenMember
              · exact Or.inl (Or.inl
                  (previous.expression conditionMember))
              · exact Or.inl (Or.inr
                  (previous.expression thenMember))
            · exact Or.inr (previous.expression elseMember)
        | index receiver index =>
            rw [expressionDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with receiverMember | indexMember
            · exact Or.inl (previous.expression receiverMember)
            · exact Or.inr (previous.expression indexMember)
        | «prefix» operator operand =>
            rw [expressionDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
        | «infix» operator left right =>
            rw [expressionDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with leftMember | rightMember
            · exact Or.inl (previous.expression leftMember)
            · exact Or.inr (previous.expression rightMember)
        | tuple elements =>
            rw [expressionDiagnosticsFuel, shape,
              List.mem_flatMap] at member ⊢
            rcases member with ⟨element, elementIn, diagnosticIn⟩
            exact ⟨element, elementIn,
              previous.expression diagnosticIn⟩
        | group inner =>
            rw [expressionDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
      · intro pattern diagnostic member
        cases shape : pattern.payload with
        | named name arguments =>
            cases arguments with
            | none => simp [patternDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [patternDiagnosticsFuel, shape,
                  List.mem_flatMap] at member ⊢
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact ⟨argument, argumentIn,
                  previous.pattern diagnosticIn⟩
        | dotConstructor marker name arguments =>
            cases arguments with
            | none => simp [patternDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [patternDiagnosticsFuel, shape,
                  List.mem_flatMap] at member ⊢
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact ⟨argument, argumentIn,
                  previous.pattern diagnosticIn⟩
        | wildcard marker =>
            simp [patternDiagnosticsFuel, shape] at member
        | literal literal =>
            simp [patternDiagnosticsFuel, shape] at member
        | comptime marker expression =>
            rw [patternDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
        | tuple elements =>
            rw [patternDiagnosticsFuel, shape,
              List.mem_flatMap] at member ⊢
            rcases member with ⟨element, elementIn, diagnosticIn⟩
            exact ⟨element, elementIn,
              previous.pattern diagnosticIn⟩
        | group inner =>
            rw [patternDiagnosticsFuel, shape] at member ⊢
            exact previous.pattern member
      · intro loopDepth body diagnostic member
        rw [bodyDiagnosticsFuel, List.mem_flatMap] at member ⊢
        rcases member with ⟨statement, statementIn, diagnosticIn⟩
        exact ⟨statement, statementIn,
          previous.statement diagnosticIn⟩
      · intro loopDepth statement diagnostic member
        cases shape : statement.payload with
        | assignment operator left right =>
            rw [statementDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with leftMember | rightMember
            · exact Or.inl (previous.expression leftMember)
            · exact Or.inr (previous.expression rightMember)
        | letBinding binding =>
            cases initializerShape : binding.payload.initializer with
            | none =>
                simp [statementDiagnosticsFuel, shape,
                  initializerShape] at member
            | some initializer =>
                simp only [statementDiagnosticsFuel, shape,
                  initializerShape] at member ⊢
                exact previous.expression member
        | block body =>
            rw [statementDiagnosticsFuel, shape] at member ⊢
            exact previous.body member
        | expression expression terminator =>
            rw [statementDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
        | «return» value terminator =>
            cases value with
            | none => simp [statementDiagnosticsFuel, shape] at member
            | some expression =>
                rw [statementDiagnosticsFuel, shape] at member ⊢
                exact previous.expression member
        | «match» scrutinees arms terminator =>
            rw [statementDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with scrutineeDiagnostic | armDiagnostic
            · apply Or.inl
              rw [List.mem_flatMap] at scrutineeDiagnostic ⊢
              rcases scrutineeDiagnostic with
                ⟨scrutinee, scrutineeIn, diagnosticIn⟩
              exact ⟨scrutinee, scrutineeIn,
                previous.expression diagnosticIn⟩
            · apply Or.inr
              rw [List.mem_flatMap] at armDiagnostic ⊢
              rcases armDiagnostic with ⟨arm, armIn, diagnosticIn⟩
              refine ⟨arm, armIn, ?_⟩
              simp only [List.mem_append] at diagnosticIn ⊢
              rcases diagnosticIn with earlierDiagnostic | bodyDiagnostic
              · rcases earlierDiagnostic with mismatchDiagnostic |
                  patternDiagnostic
                · exact Or.inl (Or.inl mismatchDiagnostic)
                · apply Or.inl
                  apply Or.inr
                  rw [List.mem_flatMap] at patternDiagnostic ⊢
                  rcases patternDiagnostic with
                    ⟨pattern, patternIn, nestedDiagnostic⟩
                  exact ⟨pattern, patternIn,
                    previous.pattern nestedDiagnostic⟩
              · exact Or.inr (previous.body bodyDiagnostic)
        | assembly slice =>
            simp [statementDiagnosticsFuel, shape] at member
        | ifThenElse condition thenBody elseBody =>
            rw [statementDiagnosticsFuel, shape] at member ⊢
            simp only [List.mem_append] at member ⊢
            rcases member with earlierDiagnostic | elseDiagnostic
            · rcases earlierDiagnostic with conditionDiagnostic |
                thenDiagnostic
              · exact Or.inl (Or.inl
                  (previous.expression conditionDiagnostic))
              · exact Or.inl (Or.inr
                  (previous.body thenDiagnostic))
            · cases elseBody with
              | none => simp at elseDiagnostic
              | some elseBody =>
                  exact Or.inr (previous.body elseDiagnostic)
        | forLoop initializers condition post body =>
            simp only [statementDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with beforeBody | bodyDiagnostic
            · rcases beforeBody with beforePost | postDiagnostic
              · rcases beforePost with initializerDiagnostic |
                  conditionDiagnostic
                · apply Or.inl
                  apply Or.inl
                  apply Or.inl
                  rw [List.mem_flatMap] at initializerDiagnostic ⊢
                  rcases initializerDiagnostic with
                    ⟨item, itemIn, diagnosticIn⟩
                  exact ⟨item, itemIn,
                    previous.forInit diagnosticIn⟩
                · exact Or.inl (Or.inl (Or.inr
                    (previous.expression conditionDiagnostic)))
              · apply Or.inl
                apply Or.inr
                rw [List.mem_flatMap] at postDiagnostic ⊢
                rcases postDiagnostic with ⟨item, itemIn, diagnosticIn⟩
                exact ⟨item, itemIn,
                  previous.forPost diagnosticIn⟩
            · exact Or.inr (previous.body bodyDiagnostic)
        | «break» terminator =>
            simpa [statementDiagnosticsFuel, shape] using member
        | «continue» terminator =>
            simpa [statementDiagnosticsFuel, shape] using member
      · intro item diagnostic member
        cases shape : item.payload with
        | letBinding binding =>
            cases initializerShape : binding.payload.initializer with
            | none =>
                simp [forInitDiagnosticsFuel, shape,
                  initializerShape] at member
            | some initializer =>
                simp only [forInitDiagnosticsFuel, shape,
                  initializerShape] at member ⊢
                exact previous.expression member
        | assignment operator left right =>
            rw [forInitDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with leftMember | rightMember
            · exact Or.inl (previous.expression leftMember)
            · exact Or.inr (previous.expression rightMember)
        | expression expression =>
            rw [forInitDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member
      · intro item diagnostic member
        cases shape : item.payload with
        | assignment operator left right =>
            rw [forPostDiagnosticsFuel, shape,
              List.mem_append] at member ⊢
            rcases member with leftMember | rightMember
            · exact Or.inl (previous.expression leftMember)
            · exact Or.inr (previous.expression rightMember)
        | expression expression =>
            rw [forPostDiagnosticsFuel, shape] at member ⊢
            exact previous.expression member

/-- Increasing traversal fuel preserves every expression diagnostic already
emitted at the smaller fuel. -/
theorem mem_expressionDiagnosticsFuel_mono
    {fuel larger : Nat} {expression : Expression}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈ expressionDiagnosticsFuel fuel expression) :
    diagnostic ∈ expressionDiagnosticsFuel larger expression := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).expression induction

/-- Increasing traversal fuel preserves every pattern diagnostic already
emitted at the smaller fuel. -/
theorem mem_patternDiagnosticsFuel_mono
    {fuel larger : Nat} {pattern : Pattern}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈ patternDiagnosticsFuel fuel pattern) :
    diagnostic ∈ patternDiagnosticsFuel larger pattern := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).pattern induction

/-- Increasing traversal fuel preserves every body diagnostic already emitted
at the smaller fuel. -/
theorem mem_bodyDiagnosticsFuel_mono
    {fuel larger loopDepth : Nat} {body : Body}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body) :
    diagnostic ∈ bodyDiagnosticsFuel larger loopDepth body := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).body induction

/-- Increasing traversal fuel preserves every statement diagnostic already
emitted at the smaller fuel. -/
theorem mem_statementDiagnosticsFuel_mono
    {fuel larger loopDepth : Nat} {statement : Statement}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈
      statementDiagnosticsFuel fuel loopDepth statement) :
    diagnostic ∈ statementDiagnosticsFuel larger loopDepth statement := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).statement induction

/-- Increasing traversal fuel preserves every `for`-initializer diagnostic
already emitted at the smaller fuel. -/
theorem mem_forInitDiagnosticsFuel_mono
    {fuel larger : Nat} {item : ForInitItem}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈ forInitDiagnosticsFuel fuel item) :
    diagnostic ∈ forInitDiagnosticsFuel larger item := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).forInit induction

/-- Increasing traversal fuel preserves every `for`-post diagnostic already
emitted at the smaller fuel. -/
theorem mem_forPostDiagnosticsFuel_mono
    {fuel larger : Nat} {item : ForPostItem}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (member : diagnostic ∈ forPostDiagnosticsFuel fuel item) :
    diagnostic ∈ forPostDiagnosticsFuel larger item := by
  induction fuelLe with
  | refl => exact member
  | @step larger fuelLe induction =>
      exact (recursiveDiagnosticsFuel_step larger).forPost induction

/-- A mismatched reached match arm emits its arity diagnostic with one unit of
statement traversal fuel. -/
theorem matchPatternArityMismatch_mem_statementDiagnosticsFuel_one
    {loopDepth : Nat} {statement : Statement}
    {scrutinees : NonemptyList Expression}
    {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
    {arm : MatchArm}
    (shape : statement.payload = .match scrutinees arms terminator)
    (armMember : arm ∈ arms.toList)
    (mismatch : arm.payload.patterns.toList.length ≠
      scrutinees.toList.length) :
    StructuralDiagnostic.matchPatternArityMismatch arm.span
        scrutinees.toList.length arm.payload.patterns.toList.length ∈
      statementDiagnosticsFuel 1 loopDepth statement := by
  rw [statementDiagnosticsFuel, shape, List.mem_append]
  apply Or.inr
  rw [List.mem_flatMap]
  refine ⟨arm, ?_, ?_⟩
  · simpa [nonemptyToList, NonemptyList.toList] using armMember
  simp only [List.mem_append]
  apply Or.inl
  apply Or.inl
  have internalMismatch :
      (nonemptyToList arm.payload.patterns).length ≠
        (nonemptyToList scrutinees).length := by
    simpa [nonemptyToList, NonemptyList.toList] using mismatch
  rw [if_neg internalMismatch]
  simp [nonemptyToList, NonemptyList.toList]

/-- A break statement at loop depth zero emits its control diagnostic with one
unit of statement traversal fuel. -/
theorem breakOutsideLoop_mem_statementDiagnosticsFuel_one
    {statement : Statement} {terminator : SourceSpan}
    (shape : statement.payload = .break terminator) :
    StructuralDiagnostic.controlOutsideLoop statement.span .breakControl ∈
      statementDiagnosticsFuel 1 0 statement := by
  simp [statementDiagnosticsFuel, shape]

/-- A continue statement at loop depth zero emits its control diagnostic with
one unit of statement traversal fuel. -/
theorem continueOutsideLoop_mem_statementDiagnosticsFuel_one
    {statement : Statement} {terminator : SourceSpan}
    (shape : statement.payload = .continue terminator) :
    StructuralDiagnostic.controlOutsideLoop statement.span .continueControl ∈
      statementDiagnosticsFuel 1 0 statement := by
  simp [statementDiagnosticsFuel, shape]

private structure RecursiveDiagnosticsFuelSound (fuel : Nat) : Prop where
  expression :
    ∀ {module : ParsedModuleV1} {expression : Expression}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.expression expression) →
      diagnostic ∈ expressionDiagnosticsFuel fuel expression →
      StructuralDiagnostic.Applies module diagnostic
  pattern :
    ∀ {module : ParsedModuleV1} {pattern : Pattern}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.pattern pattern) →
      diagnostic ∈ patternDiagnosticsFuel fuel pattern →
      StructuralDiagnostic.Applies module diagnostic
  body :
    ∀ {module : ParsedModuleV1} {loopDepth : Nat} {body : Body}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.body loopDepth body) →
      diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body →
      StructuralDiagnostic.Applies module diagnostic
  statement :
    ∀ {module : ParsedModuleV1} {loopDepth : Nat} {statement : Statement}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.statement loopDepth statement) →
      diagnostic ∈ statementDiagnosticsFuel fuel loopDepth statement →
      StructuralDiagnostic.Applies module diagnostic
  forInit :
    ∀ {module : ParsedModuleV1} {item : ForInitItem}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.forInit item) →
      diagnostic ∈ forInitDiagnosticsFuel fuel item →
      StructuralDiagnostic.Applies module diagnostic
  forPost :
    ∀ {module : ParsedModuleV1} {item : ForPostItem}
      {diagnostic : StructuralDiagnostic},
      StructuralSite.Occurs module (.forPost item) →
      diagnostic ∈ forPostDiagnosticsFuel fuel item →
      StructuralDiagnostic.Applies module diagnostic

private theorem recursiveDiagnosticsFuel_applies
    (fuel : Nat) : RecursiveDiagnosticsFuelSound fuel := by
  induction fuel with
  | zero =>
      constructor <;> intros <;> simp_all [expressionDiagnosticsFuel,
        patternDiagnosticsFuel, bodyDiagnosticsFuel,
        statementDiagnosticsFuel, forInitDiagnosticsFuel,
        forPostDiagnosticsFuel]
  | succ fuel previous =>
      constructor
      · intro module expression diagnostic occurrence member
        cases shape : expression.payload with
        | name name => simp [expressionDiagnosticsFuel, shape] at member
        | call callee arguments =>
            rw [expressionDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with calleeMember | argumentMember
            · exact previous.expression
                (.expressionCallCallee occurrence shape) calleeMember
            · rw [List.mem_flatMap] at argumentMember
              rcases argumentMember with
                ⟨argument, argumentIn, diagnosticIn⟩
              exact previous.expression
                (.expressionCallArgument occurrence shape argumentIn)
                diagnosticIn
        | select receiver field =>
            rw [expressionDiagnosticsFuel, shape] at member
            exact previous.expression
              (.expressionSelectReceiver occurrence shape) member
        | dotConstructor marker name arguments =>
            cases arguments with
            | none => simp [expressionDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [expressionDiagnosticsFuel, shape,
                  List.mem_flatMap] at member
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact previous.expression
                  (.expressionDotConstructorArgument occurrence shape
                    argumentIn)
                  diagnosticIn
        | proxy marker typeExpression =>
            simp [expressionDiagnosticsFuel, shape] at member
        | literal literal =>
            simp [expressionDiagnosticsFuel, shape] at member
        | lambda parameters returnType body =>
            rw [expressionDiagnosticsFuel, shape] at member
            exact previous.body
              (.expressionLambdaBody occurrence shape) member
        | annotation inner typeExpression =>
            rw [expressionDiagnosticsFuel, shape] at member
            exact previous.expression
              (.expressionAnnotationInner occurrence shape) member
        | keywordConditional condition thenBranch elseBranch =>
            simp only [expressionDiagnosticsFuel, shape,
              List.mem_append] at member
            rcases member with earlierMember | elseMember
            · rcases earlierMember with conditionMember | thenMember
              · exact previous.expression
                  (.expressionKeywordCondition occurrence shape)
                  conditionMember
              · exact previous.expression
                  (.expressionKeywordThen occurrence shape) thenMember
            · exact previous.expression
                (.expressionKeywordElse occurrence shape) elseMember
        | ternaryConditional condition thenBranch elseBranch =>
            simp only [expressionDiagnosticsFuel, shape,
              List.mem_append] at member
            rcases member with earlierMember | elseMember
            · rcases earlierMember with conditionMember | thenMember
              · exact previous.expression
                  (.expressionTernaryCondition occurrence shape)
                  conditionMember
              · exact previous.expression
                  (.expressionTernaryThen occurrence shape) thenMember
            · exact previous.expression
                (.expressionTernaryElse occurrence shape) elseMember
        | index receiver index =>
            rw [expressionDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with receiverMember | indexMember
            · exact previous.expression
                (.expressionIndexReceiver occurrence shape) receiverMember
            · exact previous.expression
                (.expressionIndexValue occurrence shape) indexMember
        | «prefix» operator operand =>
            rw [expressionDiagnosticsFuel, shape] at member
            exact previous.expression
              (.expressionPrefixOperand occurrence shape) member
        | «infix» operator left right =>
            rw [expressionDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with leftMember | rightMember
            · exact previous.expression
                (.expressionInfixLeft occurrence shape) leftMember
            · exact previous.expression
                (.expressionInfixRight occurrence shape) rightMember
        | tuple elements =>
            rw [expressionDiagnosticsFuel, shape,
              List.mem_flatMap] at member
            rcases member with ⟨element, elementIn, diagnosticIn⟩
            exact previous.expression
              (.expressionTupleElement occurrence shape elementIn)
              diagnosticIn
        | group inner =>
            rw [expressionDiagnosticsFuel, shape] at member
            exact previous.expression
              (.expressionGroupInner occurrence shape) member
      · intro module pattern diagnostic occurrence member
        cases shape : pattern.payload with
        | named name arguments =>
            cases arguments with
            | none => simp [patternDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [patternDiagnosticsFuel, shape,
                  List.mem_flatMap] at member
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact previous.pattern
                  (.patternNamedArgument occurrence shape (by
                    simpa [nonemptyToList, NonemptyList.toList] using
                      argumentIn))
                  diagnosticIn
        | dotConstructor marker name arguments =>
            cases arguments with
            | none => simp [patternDiagnosticsFuel, shape] at member
            | some arguments =>
                rw [patternDiagnosticsFuel, shape,
                  List.mem_flatMap] at member
                rcases member with ⟨argument, argumentIn, diagnosticIn⟩
                exact previous.pattern
                  (.patternDotConstructorArgument occurrence shape (by
                    simpa [nonemptyToList, NonemptyList.toList] using
                      argumentIn))
                  diagnosticIn
        | wildcard marker =>
            simp [patternDiagnosticsFuel, shape] at member
        | literal literal =>
            simp [patternDiagnosticsFuel, shape] at member
        | comptime marker expression =>
            rw [patternDiagnosticsFuel, shape] at member
            exact previous.expression
              (.patternComptimeExpression occurrence shape) member
        | tuple elements =>
            rw [patternDiagnosticsFuel, shape, List.mem_flatMap] at member
            rcases member with ⟨element, elementIn, diagnosticIn⟩
            exact previous.pattern
              (.patternTupleElement occurrence shape elementIn) diagnosticIn
        | group inner =>
            rw [patternDiagnosticsFuel, shape] at member
            exact previous.pattern
              (.patternGroupInner occurrence shape) member
      · intro module loopDepth body diagnostic occurrence member
        rw [bodyDiagnosticsFuel, List.mem_flatMap] at member
        rcases member with ⟨statement, statementIn, diagnosticIn⟩
        exact previous.statement
          (.bodyStatement occurrence statementIn) diagnosticIn
      · intro module loopDepth statement diagnostic occurrence member
        cases shape : statement.payload with
        | assignment operator left right =>
            rw [statementDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with leftMember | rightMember
            · exact previous.expression
                (.statementAssignmentLeft occurrence shape) leftMember
            · exact previous.expression
                (.statementAssignmentRight occurrence shape) rightMember
        | letBinding binding =>
            cases initializerShape : binding.payload.initializer with
            | none =>
                simp [statementDiagnosticsFuel, shape,
                  initializerShape] at member
            | some initializer =>
                simp only [statementDiagnosticsFuel, shape,
                  initializerShape] at member
                exact previous.expression
                  (.statementLetInitializer occurrence shape
                    initializerShape)
                  member
        | block body =>
            rw [statementDiagnosticsFuel, shape] at member
            exact previous.body (.statementBlockBody occurrence shape) member
        | expression expression terminator =>
            rw [statementDiagnosticsFuel, shape] at member
            exact previous.expression
              (.statementExpression occurrence shape) member
        | «return» value terminator =>
            cases value with
            | none => simp [statementDiagnosticsFuel, shape] at member
            | some expression =>
                rw [statementDiagnosticsFuel, shape] at member
                exact previous.expression
                  (.statementReturnValue occurrence shape) member
        | «match» scrutinees arms terminator =>
            rw [statementDiagnosticsFuel, shape,
              List.mem_append] at member
            rcases member with scrutineeDiagnostic | armDiagnostic
            · rw [List.mem_flatMap] at scrutineeDiagnostic
              rcases scrutineeDiagnostic with
                ⟨scrutinee, scrutineeIn, diagnosticIn⟩
              exact previous.expression
                (.statementMatchScrutinee occurrence shape (by
                  simpa [nonemptyToList, NonemptyList.toList] using
                    scrutineeIn))
                diagnosticIn
            · rw [List.mem_flatMap] at armDiagnostic
              rcases armDiagnostic with ⟨arm, armIn, diagnosticIn⟩
              simp only [List.mem_append] at diagnosticIn
              rcases diagnosticIn with earlierDiagnostic | bodyDiagnostic
              · rcases earlierDiagnostic with mismatchDiagnostic |
                  patternDiagnostic
                · by_cases arity :
                      (nonemptyToList arm.payload.patterns).length =
                        (nonemptyToList scrutinees).length
                  · simp [arity] at mismatchDiagnostic
                  · simp only [arity, if_false,
                      List.mem_singleton] at mismatchDiagnostic
                    rw [mismatchDiagnostic]
                    exact .matchPatternArityMismatch occurrence shape (by
                      simpa [nonemptyToList, NonemptyList.toList] using armIn)
                      (by
                        simpa [nonemptyToList, NonemptyList.toList] using
                          arity)
                · rw [List.mem_flatMap] at patternDiagnostic
                  rcases patternDiagnostic with
                    ⟨pattern, patternIn, nestedDiagnostic⟩
                  exact previous.pattern
                    (.statementMatchPattern occurrence shape (by
                      simpa [nonemptyToList, NonemptyList.toList] using armIn)
                      (by
                        simpa [nonemptyToList, NonemptyList.toList] using
                          patternIn))
                    nestedDiagnostic
              · exact previous.body
                  (.statementMatchArmBody occurrence shape (by
                    simpa [nonemptyToList, NonemptyList.toList] using armIn))
                  bodyDiagnostic
        | assembly slice =>
            simp [statementDiagnosticsFuel, shape] at member
        | ifThenElse condition thenBody elseBody =>
            rw [statementDiagnosticsFuel, shape] at member
            simp only [List.mem_append] at member
            rcases member with earlierDiagnostic | elseDiagnostic
            · rcases earlierDiagnostic with conditionDiagnostic |
                thenDiagnostic
              · exact previous.expression
                  (.statementIfCondition occurrence shape)
                  conditionDiagnostic
              · exact previous.body
                  (.statementIfThenBody occurrence shape) thenDiagnostic
            · cases elseBody with
              | none => simp at elseDiagnostic
              | some elseBody =>
                  exact previous.body
                    (.statementIfElseBody occurrence shape) elseDiagnostic
        | forLoop initializers condition post body =>
            simp only [statementDiagnosticsFuel, shape,
              List.mem_append] at member
            rcases member with beforeBody | bodyDiagnostic
            · rcases beforeBody with beforePost | postDiagnostic
              · rcases beforePost with initializerDiagnostic |
                  conditionDiagnostic
                · rw [List.mem_flatMap] at initializerDiagnostic
                  rcases initializerDiagnostic with
                    ⟨item, itemIn, diagnosticIn⟩
                  exact previous.forInit
                    (.statementForInitializer occurrence shape itemIn)
                    diagnosticIn
                · exact previous.expression
                    (.statementForCondition occurrence shape)
                    conditionDiagnostic
              · rw [List.mem_flatMap] at postDiagnostic
                rcases postDiagnostic with ⟨item, itemIn, diagnosticIn⟩
                exact previous.forPost
                  (.statementForPost occurrence shape itemIn) diagnosticIn
            · exact previous.body
                (.statementForBody occurrence shape) bodyDiagnostic
        | «break» terminator =>
            by_cases atTop : loopDepth = 0
            · subst loopDepth
              simp only [statementDiagnosticsFuel, shape, if_true,
                List.mem_singleton] at member
              rw [member]
              exact .breakOutsideLoop occurrence shape
            · simp [statementDiagnosticsFuel, shape, atTop] at member
        | «continue» terminator =>
            by_cases atTop : loopDepth = 0
            · subst loopDepth
              simp only [statementDiagnosticsFuel, shape, if_true,
                List.mem_singleton] at member
              rw [member]
              exact .continueOutsideLoop occurrence shape
            · simp [statementDiagnosticsFuel, shape, atTop] at member
      · intro module item diagnostic occurrence member
        cases shape : item.payload with
        | letBinding binding =>
            cases initializerShape : binding.payload.initializer with
            | none =>
                simp [forInitDiagnosticsFuel, shape,
                  initializerShape] at member
            | some initializer =>
                simp only [forInitDiagnosticsFuel, shape,
                  initializerShape] at member
                exact previous.expression
                  (.forInitLetInitializer occurrence shape initializerShape)
                  member
        | assignment operator left right =>
            rw [forInitDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with leftMember | rightMember
            · exact previous.expression
                (.forInitAssignmentLeft occurrence shape) leftMember
            · exact previous.expression
                (.forInitAssignmentRight occurrence shape) rightMember
        | expression expression =>
            rw [forInitDiagnosticsFuel, shape] at member
            exact previous.expression
              (.forInitExpression occurrence shape) member
      · intro module item diagnostic occurrence member
        cases shape : item.payload with
        | assignment operator left right =>
            rw [forPostDiagnosticsFuel, shape, List.mem_append] at member
            rcases member with leftMember | rightMember
            · exact previous.expression
                (.forPostAssignmentLeft occurrence shape) leftMember
            · exact previous.expression
                (.forPostAssignmentRight occurrence shape) rightMember
        | expression expression =>
            rw [forPostDiagnosticsFuel, shape] at member
            exact previous.expression
              (.forPostExpression occurrence shape) member

/-- Every diagnostic emitted while traversing a reached expression is
declaratively applicable. -/
theorem mem_expressionDiagnosticsFuel_applies
    {fuel : Nat} {module : ParsedModuleV1} {expression : Expression}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.expression expression))
    (member : diagnostic ∈ expressionDiagnosticsFuel fuel expression) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).expression occurrence member

/-- Every diagnostic emitted while traversing a reached pattern is
declaratively applicable. -/
theorem mem_patternDiagnosticsFuel_applies
    {fuel : Nat} {module : ParsedModuleV1} {pattern : Pattern}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.pattern pattern))
    (member : diagnostic ∈ patternDiagnosticsFuel fuel pattern) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).pattern occurrence member

/-- Every diagnostic emitted while traversing a reached body is declaratively
applicable. -/
theorem mem_bodyDiagnosticsFuel_applies
    {fuel loopDepth : Nat} {module : ParsedModuleV1} {body : Body}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.body loopDepth body))
    (member : diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).body occurrence member

/-- Every diagnostic emitted while traversing a reached statement is
declaratively applicable. -/
theorem mem_statementDiagnosticsFuel_applies
    {fuel loopDepth : Nat} {module : ParsedModuleV1} {statement : Statement}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.statement loopDepth statement))
    (member : diagnostic ∈
      statementDiagnosticsFuel fuel loopDepth statement) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).statement occurrence member

/-- Every diagnostic emitted while traversing a reached `for` initializer is
declaratively applicable. -/
theorem mem_forInitDiagnosticsFuel_applies
    {fuel : Nat} {module : ParsedModuleV1} {item : ForInitItem}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.forInit item))
    (member : diagnostic ∈ forInitDiagnosticsFuel fuel item) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).forInit occurrence member

/-- Every diagnostic emitted while traversing a reached `for` post item is
declaratively applicable. -/
theorem mem_forPostDiagnosticsFuel_applies
    {fuel : Nat} {module : ParsedModuleV1} {item : ForPostItem}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.forPost item))
    (member : diagnostic ∈ forPostDiagnosticsFuel fuel item) :
    StructuralDiagnostic.Applies module diagnostic :=
  (recursiveDiagnosticsFuel_applies fuel).forPost occurrence member

/-- The executable fallback return-type test is exactly the independent
grouped-unit judgment. -/
@[simp] theorem typeExprIsGroupedUnit_eq_true_iff :
    ∀ expression : TypeExpr,
      typeExprIsGroupedUnit expression = true ↔ GroupedUnit expression := by
  intro expression
  rcases expression with ⟨span, payload⟩
  cases payload with
  | tuple elements =>
      cases elements with
      | nil =>
          simp only [typeExprIsGroupedUnit]
          exact ⟨fun _ => .unitTuple span, fun _ => True.intro⟩
      | cons head tail =>
          simp only [typeExprIsGroupedUnit, Bool.false_eq_true]
          exact ⟨False.elim, fun accepted => by cases accepted⟩
  | group inner =>
      simp only [typeExprIsGroupedUnit]
      rw [typeExprIsGroupedUnit_eq_true_iff inner]
      exact ⟨fun accepted => .group span inner accepted,
        fun accepted => by cases accepted; assumption⟩
  | named name arguments =>
      simp only [typeExprIsGroupedUnit, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | proxy marker inner =>
      simp only [typeExprIsGroupedUnit, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | «function» domain codomain =>
      simp only [typeExprIsGroupedUnit, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | comptime marker inner =>
      simp only [typeExprIsGroupedUnit, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
termination_by expression => sizeOf expression

private theorem mem_fallbackDiagnostics_iff_emitted
    {fuel : Nat} {declaration : FallbackDecl}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ fallbackDiagnostics fuel declaration ↔
      (∃ marker,
        declaration.payload.public = some marker ∧
        diagnostic = StructuralDiagnostic.modifierNotAllowed
          marker.span .fallback marker.payload) ∨
      (declaration.payload.parameters ≠ [] ∧
        diagnostic = StructuralDiagnostic.fallbackHasParameters
          declaration.payload.marker.span
          declaration.payload.parameters.length) ∨
      (∃ returnType,
        declaration.payload.returnType = some returnType ∧
        ¬GroupedUnit returnType ∧
        diagnostic = StructuralDiagnostic.fallbackHasNonUnitReturn
          returnType.span) ∨
      diagnostic ∈
        bodyDiagnosticsFuel fuel 0 declaration.payload.body := by
  change diagnostic ∈
      (match declaration.payload.public with
      | none => []
      | some marker =>
          [.modifierNotAllowed marker.span .fallback marker.payload]) ++
      (if declaration.payload.parameters.isEmpty then []
      else [.fallbackHasParameters declaration.payload.marker.span
        declaration.payload.parameters.length]) ++
      (match declaration.payload.returnType with
      | none => []
      | some returnType =>
          if typeExprIsGroupedUnit returnType then []
          else [.fallbackHasNonUnitReturn returnType.span]) ++
      bodyDiagnosticsFuel fuel 0 declaration.payload.body ↔ _
  cases publicShape : declaration.payload.public with
  | none =>
      cases returnShape : declaration.payload.returnType with
      | none =>
          by_cases parametersEmpty : declaration.payload.parameters = []
          · simp [parametersEmpty]
          · simp [parametersEmpty]
      | some returnType =>
          by_cases parametersEmpty : declaration.payload.parameters = []
          · simp [parametersEmpty,
              typeExprIsGroupedUnit_eq_true_iff]
          · simp [parametersEmpty, typeExprIsGroupedUnit_eq_true_iff]
  | some marker =>
      cases returnShape : declaration.payload.returnType with
      | none =>
          by_cases parametersEmpty : declaration.payload.parameters = []
          · simp [parametersEmpty]
          · simp [parametersEmpty]
      | some returnType =>
          by_cases parametersEmpty : declaration.payload.parameters = []
          · simp [parametersEmpty, typeExprIsGroupedUnit_eq_true_iff]
          · simp [parametersEmpty, typeExprIsGroupedUnit_eq_true_iff]

/-- The fallback collector emits exactly its public-modifier, parameter-list,
return-type, and nested-body diagnostics. -/
theorem mem_fallbackDiagnostics_iff
    {fuel : Nat} {declaration : FallbackDecl}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ fallbackDiagnostics fuel declaration ↔
      (∃ marker,
        declaration.payload.public = some marker ∧
        StructuralDiagnostic.modifierNotAllowed
          marker.span .fallback marker.payload = diagnostic) ∨
      (declaration.payload.parameters ≠ [] ∧
        StructuralDiagnostic.fallbackHasParameters
          declaration.payload.marker.span
          declaration.payload.parameters.length = diagnostic) ∨
      (∃ returnType,
        declaration.payload.returnType = some returnType ∧
        ¬GroupedUnit returnType ∧
        StructuralDiagnostic.fallbackHasNonUnitReturn
          returnType.span = diagnostic) ∨
      diagnostic ∈
        bodyDiagnosticsFuel fuel 0 declaration.payload.body := by
  rw [mem_fallbackDiagnostics_iff_emitted]
  constructor
  · intro member
    rcases member with modifier | parameters | returnType | body
    · rcases modifier with ⟨marker, selected, diagnosticEq⟩
      exact Or.inl ⟨marker, selected, diagnosticEq.symm⟩
    · rcases parameters with ⟨nonempty, diagnosticEq⟩
      exact Or.inr (Or.inl ⟨nonempty, diagnosticEq.symm⟩)
    · rcases returnType with
        ⟨returnType, selected, notUnit, diagnosticEq⟩
      exact Or.inr (Or.inr (Or.inl
        ⟨returnType, selected, notUnit, diagnosticEq.symm⟩))
    · exact Or.inr (Or.inr (Or.inr body))
  · intro member
    rcases member with modifier | parameters | returnType | body
    · rcases modifier with ⟨marker, selected, diagnosticEq⟩
      exact Or.inl ⟨marker, selected, diagnosticEq.symm⟩
    · rcases parameters with ⟨nonempty, diagnosticEq⟩
      exact Or.inr (Or.inl ⟨nonempty, diagnosticEq.symm⟩)
    · rcases returnType with
        ⟨returnType, selected, notUnit, diagnosticEq⟩
      exact Or.inr (Or.inr (Or.inl
        ⟨returnType, selected, notUnit, diagnosticEq.symm⟩))
    · exact Or.inr (Or.inr (Or.inr body))

private theorem mem_constructorDiagnostics_iff_emitted
    {fuel : Nat} {declaration : ContractConstructorDecl}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ constructorDiagnostics fuel declaration ↔
      (∃ marker,
        declaration.payload.public = some marker ∧
        diagnostic = StructuralDiagnostic.modifierNotAllowed marker.span
          .contractConstructor marker.payload) ∨
      (∃ parameter,
        parameter ∈ declaration.payload.parameters ∧
        parameter.payload.type = none ∧
        diagnostic = StructuralDiagnostic.requiredParameterTypeMissing
          parameter.payload.name.span .contractConstructor) ∨
      diagnostic ∈
        bodyDiagnosticsFuel fuel 0 declaration.payload.body := by
  change diagnostic ∈
      (match declaration.payload.public with
      | none => []
      | some marker =>
          [.modifierNotAllowed marker.span .contractConstructor
            marker.payload]) ++
      missingParameterTypeDiagnostics .contractConstructor
        declaration.payload.parameters ++
      bodyDiagnosticsFuel fuel 0 declaration.payload.body ↔ _
  have missingIff :
      diagnostic ∈ missingParameterTypeDiagnostics .contractConstructor
          declaration.payload.parameters ↔
        ∃ parameter,
          parameter ∈ declaration.payload.parameters ∧
          parameter.payload.type = none ∧
          diagnostic = StructuralDiagnostic.requiredParameterTypeMissing
            parameter.payload.name.span .contractConstructor := by
    rw [mem_missingParameterTypeDiagnostics_iff]
    constructor
    · rintro ⟨parameter, parameterMember, missing, diagnosticEq⟩
      exact ⟨parameter, parameterMember, missing, diagnosticEq.symm⟩
    · rintro ⟨parameter, parameterMember, missing, diagnosticEq⟩
      exact ⟨parameter, parameterMember, missing, diagnosticEq.symm⟩
  cases publicShape : declaration.payload.public with
  | none =>
      simp [missingIff]
  | some marker =>
      simp [missingIff]

/-- The constructor collector emits exactly its public-modifier,
missing-parameter-type, and nested-body diagnostics. -/
theorem mem_constructorDiagnostics_iff
    {fuel : Nat} {declaration : ContractConstructorDecl}
    {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ constructorDiagnostics fuel declaration ↔
      (∃ marker,
        declaration.payload.public = some marker ∧
        StructuralDiagnostic.modifierNotAllowed marker.span
          .contractConstructor marker.payload = diagnostic) ∨
      (∃ parameter,
        parameter ∈ declaration.payload.parameters ∧
        parameter.payload.type = none ∧
        StructuralDiagnostic.requiredParameterTypeMissing
          parameter.payload.name.span .contractConstructor = diagnostic) ∨
      diagnostic ∈
        bodyDiagnosticsFuel fuel 0 declaration.payload.body := by
  rw [mem_constructorDiagnostics_iff_emitted]
  constructor
  · intro member
    rcases member with modifier | parameter | body
    · rcases modifier with ⟨marker, selected, diagnosticEq⟩
      exact Or.inl ⟨marker, selected, diagnosticEq.symm⟩
    · rcases parameter with
        ⟨parameter, parameterMember, missing, diagnosticEq⟩
      exact Or.inr (Or.inl
        ⟨parameter, parameterMember, missing, diagnosticEq.symm⟩)
    · exact Or.inr (Or.inr body)
  · intro member
    rcases member with modifier | parameter | body
    · rcases modifier with ⟨marker, selected, diagnosticEq⟩
      exact Or.inl ⟨marker, selected, diagnosticEq.symm⟩
    · rcases parameter with
        ⟨parameter, parameterMember, missing, diagnosticEq⟩
      exact Or.inr (Or.inl
        ⟨parameter, parameterMember, missing, diagnosticEq.symm⟩)
    · exact Or.inr (Or.inr body)

section StructuralFuelRouting

open StructureFuelDepth

private def EmitsAt
    (node : RecursiveAstNode) (fuel : Nat)
    (diagnostic : StructuralDiagnostic) : Prop :=
  match node with
  | .expression expression =>
      diagnostic ∈ expressionDiagnosticsFuel fuel expression
  | .pattern pattern =>
      diagnostic ∈ patternDiagnosticsFuel fuel pattern
  | .body loopDepth body =>
      diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body
  | .statement loopDepth statement =>
      diagnostic ∈ statementDiagnosticsFuel fuel loopDepth statement
  | .forInit item =>
      diagnostic ∈ forInitDiagnosticsFuel fuel item
  | .forPost item =>
      diagnostic ∈ forPostDiagnosticsFuel fuel item

private theorem emitsAt_mono
    {node : RecursiveAstNode} {fuel larger : Nat}
    {diagnostic : StructuralDiagnostic}
    (fuelLe : fuel ≤ larger)
    (emits : EmitsAt node fuel diagnostic) :
    EmitsAt node larger diagnostic := by
  cases node with
  | expression expression =>
      exact mem_expressionDiagnosticsFuel_mono fuelLe emits
  | pattern pattern =>
      exact mem_patternDiagnosticsFuel_mono fuelLe emits
  | body loopDepth body =>
      exact mem_bodyDiagnosticsFuel_mono fuelLe emits
  | statement loopDepth statement =>
      exact mem_statementDiagnosticsFuel_mono fuelLe emits
  | forInit item =>
      exact mem_forInitDiagnosticsFuel_mono fuelLe emits
  | forPost item =>
      exact mem_forPostDiagnosticsFuel_mono fuelLe emits

private theorem emitsAt_parent
    {parent child : RecursiveAstNode}
    (edge : RecursiveAstChild parent child)
    {fuel : Nat} {diagnostic : StructuralDiagnostic}
    (emits : EmitsAt child fuel diagnostic) :
    EmitsAt parent (fuel + 1) diagnostic := by
  cases edge <;>
    simp_all [EmitsAt, expressionDiagnosticsFuel,
      patternDiagnosticsFuel, bodyDiagnosticsFuel,
      statementDiagnosticsFuel, forInitDiagnosticsFuel,
      forPostDiagnosticsFuel, nonemptyToList]
  case expressionCallArgument =>
    exact Or.inr ⟨_, ‹_›, emits⟩
  case expressionDotConstructorArgument =>
    exact ⟨_, ‹_›, emits⟩
  case expressionTupleElement =>
    exact ⟨_, ‹_›, emits⟩
  case patternNamedArgument =>
    rcases ‹_ = _ ∨ _› with rfl | member
    · exact Or.inl emits
    · exact Or.inr ⟨_, member, emits⟩
  case patternDotConstructorArgument =>
    rcases ‹_ = _ ∨ _› with rfl | member
    · exact Or.inl emits
    · exact Or.inr ⟨_, member, emits⟩
  case patternTupleElement =>
    exact ⟨_, ‹_›, emits⟩
  case bodyStatement =>
    exact ⟨_, ‹_›, emits⟩
  case statementMatchScrutinee =>
    rcases ‹_ = _ ∨ _› with rfl | member
    · exact Or.inl emits
    · exact Or.inr (Or.inl ⟨_, member, emits⟩)
  case statementMatchPattern armMember patternMember =>
    rcases armMember with rfl | armMember
    · rcases patternMember with rfl | patternMember
      · exact Or.inr (Or.inr (Or.inr (Or.inl emits)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨_, patternMember, emits⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨_, armMember, by
          rcases patternMember with rfl | patternMember
          · exact Or.inr (Or.inl emits)
          · exact Or.inr (Or.inr (Or.inl
              ⟨_, patternMember, emits⟩))
        ⟩)))))
  case statementMatchBody =>
    rcases ‹_ = _ ∨ _› with rfl | armMember
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl emits)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨_, armMember, Or.inr (Or.inr (Or.inr emits))⟩)))))
  case statementForInitializer =>
    exact Or.inl ⟨_, ‹_›, emits⟩
  case statementForPost =>
    exact Or.inr (Or.inr (Or.inl ⟨_, ‹_›, emits⟩))

private theorem emitsAt_mem_diagnosticCandidates_of_root
    {module : ParsedModuleV1} {node : RecursiveAstNode}
    (root : RecursiveAstRoot module node)
    {diagnostic : StructuralDiagnostic}
    (emits : EmitsAt node (astNodeMeasure module + 1) diagnostic) :
    diagnostic ∈ diagnosticCandidates module := by
  change diagnostic ∈ module.payload.items.flatMap
    (topItemDiagnostics (astNodeMeasure module + 1))
  rw [List.mem_flatMap]
  cases root with
  | topLevelFunction member =>
      refine ⟨_, member, ?_⟩
      simp only [topItemDiagnostics, functionDiagnostics]
      change diagnostic ∈ (_ ++ _) ++
        bodyDiagnosticsFuel (astNodeMeasure module + 1) 0 _
      rw [List.mem_append, List.mem_append]
      exact Or.inr emits
  | instanceMethod itemMember methodMember =>
      refine ⟨_, itemMember, ?_⟩
      simp only [topItemDiagnostics]
      rw [List.mem_flatMap]
      refine ⟨_, methodMember, ?_⟩
      simp only [functionDiagnostics]
      change diagnostic ∈ (_ ++ _) ++
        bodyDiagnosticsFuel (astNodeMeasure module + 1) 0 _
      rw [List.mem_append, List.mem_append]
      exact Or.inr emits
  | contractFieldInitializer itemMember memberMember initializer_eq =>
      refine ⟨_, itemMember, ?_⟩
      simp only [topItemDiagnostics, contractDiagnostics]
      rw [List.mem_flatMap]
      refine ⟨_, memberMember, ?_⟩
      simp only [contractMemberDiagnostics]
      rw [initializer_eq]
      exact emits
  | contractFunction itemMember memberMember =>
      refine ⟨_, itemMember, ?_⟩
      simp only [topItemDiagnostics, contractDiagnostics]
      rw [List.mem_flatMap]
      refine ⟨_, memberMember, ?_⟩
      simp only [contractMemberDiagnostics]
      change diagnostic ∈ _ ++
        bodyDiagnosticsFuel (astNodeMeasure module + 1) 0 _
      rw [List.mem_append]
      exact Or.inr emits
  | fallback itemMember memberMember =>
      refine ⟨_, itemMember, ?_⟩
      simp only [topItemDiagnostics, contractDiagnostics]
      rw [List.mem_flatMap]
      refine ⟨_, memberMember, ?_⟩
      simp only [contractMemberDiagnostics]
      exact mem_fallbackDiagnostics_iff.mpr
        (Or.inr (Or.inr (Or.inr emits)))
  | constructor itemMember memberMember =>
      refine ⟨_, itemMember, ?_⟩
      simp only [topItemDiagnostics, contractDiagnostics]
      rw [List.mem_flatMap]
      refine ⟨_, memberMember, ?_⟩
      simp only [contractMemberDiagnostics]
      exact mem_constructorDiagnostics_iff.mpr
        (Or.inr (Or.inr emits))

private theorem emitsAt_mem_diagnosticCandidates_of_path
    {module : ParsedModuleV1} {node : RecursiveAstNode} {depth fuel : Nat}
    {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module node depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (emits : EmitsAt node fuel diagnostic) :
    diagnostic ∈ diagnosticCandidates module := by
  induction path generalizing fuel with
  | root root =>
      exact emitsAt_mem_diagnosticCandidates_of_root root
        (emitsAt_mono (by omega) emits)
  | @child parent child depth parentPath edge induction =>
      exact induction (fuel := fuel + 1) (by omega)
        (emitsAt_parent edge emits)

/-- An expression diagnostic emitted within a module-bounded structural path
is an executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_expressionDiagnosticsFuel
    {module : ParsedModuleV1} {expression : Expression}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.expression expression) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈ expressionDiagnosticsFuel fuel expression) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

/-- A pattern diagnostic emitted within a module-bounded structural path is an
executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_patternDiagnosticsFuel
    {module : ParsedModuleV1} {pattern : Pattern}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.pattern pattern) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈ patternDiagnosticsFuel fuel pattern) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

/-- A body diagnostic emitted within a module-bounded structural path is an
executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_bodyDiagnosticsFuel
    {module : ParsedModuleV1} {loopDepth : Nat} {body : Body}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.body loopDepth body) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈ bodyDiagnosticsFuel fuel loopDepth body) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

/-- A statement diagnostic emitted within a module-bounded structural path is
an executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel
    {module : ParsedModuleV1} {loopDepth : Nat} {statement : Statement}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.statement loopDepth statement) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈
      statementDiagnosticsFuel fuel loopDepth statement) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

/-- A `for`-initializer diagnostic emitted within a module-bounded structural
path is an executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_forInitDiagnosticsFuel
    {module : ParsedModuleV1} {item : ForInitItem}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.forInit item) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈ forInitDiagnosticsFuel fuel item) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

/-- A `for`-post diagnostic emitted within a module-bounded structural path is
an executable diagnostic candidate of that module. -/
theorem mem_diagnosticCandidates_of_mem_forPostDiagnosticsFuel
    {module : ParsedModuleV1} {item : ForPostItem}
    {depth fuel : Nat} {diagnostic : StructuralDiagnostic}
    (path : StructuralFuelPath module (.forPost item) depth)
    (fuelBound : fuel + depth ≤ astNodeMeasure module + 1)
    (member : diagnostic ∈ forPostDiagnosticsFuel fuel item) :
    diagnostic ∈ diagnosticCandidates module :=
  emitsAt_mem_diagnosticCandidates_of_path path fuelBound member

end StructuralFuelRouting

/-- Every diagnostic emitted for a reached fallback declaration is
declaratively applicable. -/
theorem mem_fallbackDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1}
    {declaration : FallbackDecl} {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module (.fallback declaration))
    (member : diagnostic ∈ fallbackDiagnostics fuel declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_fallbackDiagnostics_iff] at member
  rcases member with modifier | parameters | returnType | body
  · rcases modifier with ⟨marker, selected, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .fallbackModifierNotAllowed occurrence selected
  · rcases parameters with ⟨nonempty, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .fallbackHasParameters occurrence nonempty
  · rcases returnType with
      ⟨returnType, selected, notUnit, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .fallbackHasNonUnitReturn occurrence selected notUnit
  · exact mem_bodyDiagnosticsFuel_applies
      occurrence.fallbackBody_of_fallback body

/-- Every diagnostic emitted for a reached contract constructor is
declaratively applicable. -/
theorem mem_constructorDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1}
    {declaration : ContractConstructorDecl}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.contractConstructor declaration))
    (member : diagnostic ∈ constructorDiagnostics fuel declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_constructorDiagnostics_iff] at member
  rcases member with modifier | parameter | body
  · rcases modifier with ⟨marker, selected, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .constructorModifierNotAllowed occurrence selected
  · rcases parameter with
      ⟨parameter, parameterMember, missing, diagnosticEq⟩
    rw [← diagnosticEq]
    exact .constructorParameterTypeMissing
      occurrence parameterMember missing
  · exact mem_bodyDiagnosticsFuel_applies
      occurrence.constructorBody_of_constructor body

/-- Every diagnostic emitted for a function whose signature and body are
reached is declaratively applicable. -/
theorem mem_functionDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1}
    {modifierContext : Option ModifierContext}
    {parameterContext : ParameterContext}
    {declaration : FunctionDecl} {diagnostic : StructuralDiagnostic}
    (signatureOccurrence : StructuralSite.Occurs module
      (.signature modifierContext parameterContext
        declaration.payload.signature))
    (bodyOccurrence : StructuralSite.Occurs module
      (.body 0 declaration.payload.body))
    (member : diagnostic ∈ functionDiagnostics fuel modifierContext
      parameterContext declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases modifierContext with
  | none =>
      change diagnostic ∈
        missingParameterTypeDiagnostics parameterContext
            declaration.payload.signature.payload.parameters ++
          bodyDiagnosticsFuel fuel 0 declaration.payload.body at member
      rw [List.mem_append] at member
      rcases member with parameterMember | bodyMember
      · exact mem_missingParameterTypeDiagnostics_applies
          signatureOccurrence parameterMember
      · exact mem_bodyDiagnosticsFuel_applies bodyOccurrence bodyMember
  | some context =>
      change diagnostic ∈
        (disallowedSignatureModifierDiagnostics context
            declaration.payload.signature ++
          missingParameterTypeDiagnostics parameterContext
            declaration.payload.signature.payload.parameters) ++
          bodyDiagnosticsFuel fuel 0 declaration.payload.body at member
      simp only [List.mem_append] at member
      rcases member with signatureMember | bodyMember
      · rcases signatureMember with modifierMember | parameterMember
        · exact mem_disallowedSignatureModifierDiagnostics_applies
            signatureOccurrence modifierMember
        · exact mem_missingParameterTypeDiagnostics_applies
            signatureOccurrence parameterMember
      · exact mem_bodyDiagnosticsFuel_applies bodyOccurrence bodyMember

/-- Every diagnostic emitted for a reached class-method signature is
declaratively applicable. -/
theorem mem_classMethodDiagnostics_applies
    {module : ParsedModuleV1} {declaration : ClassMethodDecl}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.signature (some .classMethod) .classMethod
        declaration.payload.signature))
    (member : diagnostic ∈ classMethodDiagnostics declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  change diagnostic ∈
    disallowedSignatureModifierDiagnostics .classMethod
        declaration.payload.signature ++
      missingParameterTypeDiagnostics .classMethod
        declaration.payload.signature.payload.parameters at member
  rw [List.mem_append] at member
  rcases member with modifierMember | parameterMember
  · exact mem_disallowedSignatureModifierDiagnostics_applies
      occurrence modifierMember
  · exact mem_missingParameterTypeDiagnostics_applies
      occurrence parameterMember

/-- Every diagnostic emitted for a reached member of a top-level contract is
declaratively applicable. -/
theorem mem_contractMemberDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1} {item : TopItem}
    {declaration : ContractDecl} {contractMember : ContractMember}
    {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (itemShape : item.payload = .contractDecl declaration)
    (contractMemberMember : contractMember ∈ declaration.payload.members)
    (diagnosticMember : diagnostic ∈
      contractMemberDiagnostics fuel contractMember) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases memberShape : contractMember.payload with
  | dataDecl dataDeclaration =>
      simp [contractMemberDiagnostics, memberShape] at diagnosticMember
  | typeAlias typeAliasDeclaration =>
      simp [contractMemberDiagnostics, memberShape] at diagnosticMember
  | field fieldDeclaration =>
      cases initializerShape : fieldDeclaration.payload.initializer with
      | none =>
          simp [contractMemberDiagnostics, memberShape,
            initializerShape] at diagnosticMember
      | some initializer =>
          have expressionMember :
              diagnostic ∈ expressionDiagnosticsFuel fuel initializer := by
            simpa [contractMemberDiagnostics, memberShape,
              initializerShape] using diagnosticMember
          exact mem_expressionDiagnosticsFuel_applies
            (.contractFieldInitializer itemMember itemShape
              contractMemberMember memberShape initializerShape)
            expressionMember
  | «function» functionDeclaration =>
      have functionMember : diagnostic ∈
          functionDiagnostics fuel none .contractFunction
            functionDeclaration := by
        simpa [contractMemberDiagnostics, memberShape] using diagnosticMember
      exact mem_functionDiagnostics_applies
        (.contractFunctionSignature itemMember itemShape
          contractMemberMember memberShape)
        (.contractFunctionBody itemMember itemShape
          contractMemberMember memberShape)
        functionMember
  | fallback fallbackDeclaration =>
      have fallbackMember : diagnostic ∈
          fallbackDiagnostics fuel fallbackDeclaration := by
        simpa [contractMemberDiagnostics, memberShape] using diagnosticMember
      exact mem_fallbackDiagnostics_applies
        (.fallbackDeclaration itemMember itemShape
          contractMemberMember memberShape)
        fallbackMember
  | constructor constructorDeclaration =>
      have constructorMember : diagnostic ∈
          constructorDiagnostics fuel constructorDeclaration := by
        simpa [contractMemberDiagnostics, memberShape] using diagnosticMember
      exact mem_constructorDiagnostics_applies
        (.constructorDeclaration itemMember itemShape
          contractMemberMember memberShape)
        constructorMember

/-- Every diagnostic emitted for a reached top-level contract declaration is
declaratively applicable. -/
theorem mem_contractDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1} {item : TopItem}
    {declaration : ContractDecl} {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (itemShape : item.payload = .contractDecl declaration)
    (member : diagnostic ∈ contractDiagnostics fuel declaration) :
    StructuralDiagnostic.Applies module diagnostic := by
  rw [contractDiagnostics, List.mem_flatMap] at member
  rcases member with
    ⟨contractMember, contractMemberMember, diagnosticMember⟩
  exact mem_contractMemberDiagnostics_applies
    itemMember itemShape contractMemberMember diagnosticMember

/-- Every diagnostic emitted for a reached top-level item is declaratively
applicable. -/
theorem mem_topItemDiagnostics_applies
    {fuel : Nat} {module : ParsedModuleV1} {item : TopItem}
    {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (member : diagnostic ∈ topItemDiagnostics fuel item) :
    StructuralDiagnostic.Applies module diagnostic := by
  cases itemShape : item.payload with
  | importDecl declaration =>
      rw [topItemDiagnostics, itemShape] at member
      exact mem_importDiagnostics_applies itemMember itemShape member
  | exportDecl declaration =>
      rw [topItemDiagnostics, itemShape] at member
      exact mem_exportDiagnostics_applies itemMember itemShape member
  | pragmaDecl declaration =>
      rw [topItemDiagnostics, itemShape] at member
      exact mem_pragmaDiagnostics_top_applies itemMember itemShape member
  | dataDecl declaration =>
      simp [topItemDiagnostics, itemShape] at member
  | typeAliasDecl declaration =>
      simp [topItemDiagnostics, itemShape] at member
  | classDecl declaration =>
      rw [topItemDiagnostics, itemShape, List.mem_flatMap] at member
      rcases member with ⟨method, methodMember, diagnosticMember⟩
      exact mem_classMethodDiagnostics_applies
        (.classMethodSignature itemMember itemShape methodMember)
        diagnosticMember
  | instanceDecl declaration =>
      rw [topItemDiagnostics, itemShape, List.mem_flatMap] at member
      rcases member with ⟨method, methodMember, diagnosticMember⟩
      exact mem_functionDiagnostics_applies
        (.instanceMethodSignature itemMember itemShape methodMember)
        (.instanceMethodBody itemMember itemShape methodMember)
        diagnosticMember
  | contractDecl declaration =>
      rw [topItemDiagnostics, itemShape] at member
      exact mem_contractDiagnostics_applies itemMember itemShape member
  | functionDecl declaration =>
      rw [topItemDiagnostics, itemShape] at member
      exact mem_functionDiagnostics_applies
        (.topFunctionSignature itemMember itemShape)
        (.topFunctionBody itemMember itemShape)
        member

/-- Every executable structural candidate is declaratively applicable to its
containing module. -/
theorem mem_diagnosticCandidates_applies
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (member : diagnostic ∈ diagnosticCandidates module) :
    StructuralDiagnostic.Applies module diagnostic := by
  change diagnostic ∈ module.payload.items.flatMap
    (topItemDiagnostics (astNodeMeasure module + 1)) at member
  rw [List.mem_flatMap] at member
  rcases member with ⟨item, itemMember, diagnosticMember⟩
  exact mem_topItemDiagnostics_applies itemMember diagnosticMember

private theorem mem_diagnosticCandidates_of_mem_topItemDiagnostics
    {module : ParsedModuleV1} {item : TopItem}
    {diagnostic : StructuralDiagnostic}
    (itemMember : item ∈ module.payload.items)
    (diagnosticMember : diagnostic ∈
      topItemDiagnostics (astNodeMeasure module + 1) item) :
    diagnostic ∈ diagnosticCandidates module := by
  change diagnostic ∈ module.payload.items.flatMap
    (topItemDiagnostics (astNodeMeasure module + 1))
  rw [List.mem_flatMap]
  exact ⟨item, itemMember, diagnosticMember⟩

private def nonrecursiveDiagnosticsAt
    (fuel : Nat) : StructuralSite → List StructuralDiagnostic
  | .importSelection selection => importSelectionDiagnostics selection
  | .hidingClause clause => hidingDiagnostics clause
  | .localExportList selection => localExportDiagnostics selection
  | .remoteExportSelection selection => remoteExportDiagnostics selection
  | .exportItem item => exportItemDiagnostics item
  | .pragma declaration => pragmaDiagnostics declaration
  | .signature modifierContext parameterContext signature =>
      (match modifierContext with
      | none => []
      | some context =>
          disallowedSignatureModifierDiagnostics context signature) ++
        missingParameterTypeDiagnostics parameterContext
          signature.payload.parameters
  | .fallback declaration => fallbackDiagnostics fuel declaration
  | .contractConstructor declaration =>
      constructorDiagnostics fuel declaration
  | _ => []

private theorem mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt
    {module : ParsedModuleV1} {site : StructuralSite}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module site)
    (diagnosticMember : diagnostic ∈
      nonrecursiveDiagnosticsAt (astNodeMeasure module + 1) site) :
    diagnostic ∈ diagnosticCandidates module := by
  induction occurrence <;>
    simp only [nonrecursiveDiagnosticsAt, List.not_mem_nil] at diagnosticMember
  case importSelectionTop item declaration selection hidingClause
      itemMember itemShape modeShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp [topItemDiagnostics, itemShape, importDiagnostics, modeShape,
      diagnosticMember]
  case hidingClauseTop item declaration selection clause itemMember itemShape
      modeShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp [topItemDiagnostics, itemShape, importDiagnostics, modeShape,
      diagnosticMember]
  case localExportListTop item declaration selection itemMember itemShape
      modeShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simpa [topItemDiagnostics, itemShape, exportDiagnostics, modeShape] using
      diagnosticMember
  case remoteExportSelectionTop item declaration moduleRef selection itemMember
      itemShape modeShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simpa [topItemDiagnostics, itemShape, exportDiagnostics, modeShape] using
      diagnosticMember
  case localExportItem selection entry item selectionOccurs entryMember
      entryShape induction =>
    apply induction
    change diagnostic ∈ localExportDiagnostics selection
    rw [mem_localExportDiagnostics_iff]
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    exact ⟨item,
      mem_localExportItems_iff_entry.mpr ⟨entry, entryMember, entryShape⟩,
      diagnosticMember⟩
  case remoteExportItem selection entries entry item selectionOccurs
      selectionShape entryMember entryShape induction =>
    apply induction
    change diagnostic ∈ remoteExportDiagnostics selection
    rw [mem_remoteExportDiagnostics_braced_iff selectionShape]
    apply Or.inr
    apply Or.inr
    apply Or.inr
    exact ⟨item,
      mem_remoteExportItems_iff_entry.mpr ⟨entry, entryMember, entryShape⟩,
      diagnosticMember⟩
  case pragmaTop item declaration itemMember itemShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simpa [topItemDiagnostics, itemShape] using diagnosticMember
  case topFunctionSignature item declaration itemMember itemShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape, functionDiagnostics]
    rw [List.mem_append]
    exact Or.inl diagnosticMember
  case classMethodSignature item declaration method itemMember itemShape
      methodMember =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape]
    rw [List.mem_flatMap]
    exact ⟨method, methodMember, by
      simpa [classMethodDiagnostics] using diagnosticMember⟩
  case instanceMethodSignature item declaration method itemMember itemShape
      methodMember =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape]
    rw [List.mem_flatMap]
    refine ⟨method, methodMember, ?_⟩
    simp only [functionDiagnostics]
    rw [List.mem_append]
    exact Or.inl diagnosticMember
  case contractFunctionSignature item declaration contractMember
      functionDeclaration itemMember itemShape contractMemberMember
      memberShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape, contractDiagnostics]
    rw [List.mem_flatMap]
    refine ⟨contractMember, contractMemberMember, ?_⟩
    simp only [contractMemberDiagnostics, memberShape, functionDiagnostics]
    rw [List.mem_append]
    exact Or.inl diagnosticMember
  case fallbackDeclaration item declaration contractMember
      fallbackDeclaration itemMember itemShape contractMemberMember
      memberShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape, contractDiagnostics]
    rw [List.mem_flatMap]
    exact ⟨contractMember, contractMemberMember, by
      simpa [contractMemberDiagnostics, memberShape] using diagnosticMember⟩
  case constructorDeclaration item declaration contractMember
      constructorDeclaration itemMember itemShape contractMemberMember
      memberShape =>
    apply mem_diagnosticCandidates_of_mem_topItemDiagnostics itemMember
    simp only [topItemDiagnostics, itemShape, contractDiagnostics]
    rw [List.mem_flatMap]
    exact ⟨contractMember, contractMemberMember, by
      simpa [contractMemberDiagnostics, memberShape] using diagnosticMember⟩

private theorem mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel_one
    {module : ParsedModuleV1} {loopDepth : Nat} {statement : Statement}
    {diagnostic : StructuralDiagnostic}
    (occurrence : StructuralSite.Occurs module
      (.statement loopDepth statement))
    (diagnosticMember : diagnostic ∈
      statementDiagnosticsFuel 1 loopDepth statement) :
    diagnostic ∈ diagnosticCandidates module := by
  rcases occurrence.statement_fuelPath with ⟨depth, path⟩
  apply mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel
    (fuel := 1) path
  · have depthBound := path.depth_lt_astNodeMeasure
    omega
  · exact diagnosticMember

/-- Every declaratively applicable diagnostic is an executable candidate. -/
theorem applies_mem_diagnosticCandidates
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (applies : StructuralDiagnostic.Applies module diagnostic) :
    diagnostic ∈ diagnosticCandidates module := by
  cases applies with
  | emptyImportSelection occurrence empty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_importSelectionDiagnostics_iff]
      exact Or.inl ⟨empty, rfl⟩
  | mixedImportWildcard occurrence mixed least =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_importSelectionDiagnostics_iff]
      exact Or.inr (Or.inl ⟨mixed, _, least, rfl⟩)
  | duplicateImportSourceName occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_importSelectionDiagnostics_iff]
      exact Or.inr (Or.inr (Or.inl ⟨_, duplicate, rfl⟩))
  | duplicateImportLocalName occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_importSelectionDiagnostics_iff]
      exact Or.inr (Or.inr (Or.inr ⟨_, duplicate, rfl⟩))
  | emptyHidingClause occurrence empty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_hidingDiagnostics_iff]
      exact Or.inl ⟨empty, rfl⟩
  | duplicateHiddenName occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_hidingDiagnostics_iff]
      exact Or.inr ⟨_, duplicate, rfl⟩
  | emptyLocalExportList occurrence empty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_localExportDiagnostics_iff]
      exact Or.inl ⟨empty, rfl⟩
  | emptyRemoteExportList entries occurrence braced empty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt,
        mem_remoteExportDiagnostics_braced_iff braced]
      exact Or.inl ⟨empty, rfl⟩
  | mixedLocalExportWildcard occurrence mixed least =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_localExportDiagnostics_iff]
      exact Or.inr (Or.inl ⟨mixed, _, least, rfl⟩)
  | mixedRemoteExportWildcard occurrence braced mixed least =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt,
        mem_remoteExportDiagnostics_braced_iff braced]
      exact Or.inr (Or.inl ⟨mixed, _, least, rfl⟩)
  | duplicateLocalExportName occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_localExportDiagnostics_iff]
      exact Or.inr (Or.inr (Or.inl ⟨_, duplicate, rfl⟩))
  | duplicateRemoteExportName occurrence braced duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt,
        mem_remoteExportDiagnostics_braced_iff braced]
      exact Or.inr (Or.inr (Or.inl ⟨_, duplicate, rfl⟩))
  | duplicateExportModuleReference occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_localExportDiagnostics_iff]
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨_, duplicate, rfl⟩)))
  | duplicateExportConstructor occurrence selectionPresent named duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_exportItemDiagnostics_iff]
      exact ⟨_, _, _, selectionPresent, named, duplicate, rfl⟩
  | matchPatternArityMismatch occurrence shape armMember mismatch =>
      apply mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel_one
        occurrence
      exact matchPatternArityMismatch_mem_statementDiagnosticsFuel_one
        shape armMember mismatch
  | emptyGenericPragmaTargets occurrence kind empty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_pragmaDiagnostics_iff]
      exact Or.inl ⟨kind, empty, rfl⟩
  | duplicatePragmaTarget occurrence duplicate =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_pragmaDiagnostics_iff]
      exact Or.inr ⟨_, duplicate, rfl⟩
  | signatureModifierNotAllowed occurrence selected =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, List.mem_append]
      apply Or.inl
      rw [mem_disallowedSignatureModifierDiagnostics_iff]
      cases selected with
      | publicMarker selected =>
          exact Or.inl ⟨_, selected, rfl⟩
      | payableMarker selected =>
          exact Or.inr ⟨_, selected, rfl⟩
  | fallbackModifierNotAllowed occurrence selected =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_fallbackDiagnostics_iff]
      exact Or.inl ⟨_, selected, rfl⟩
  | constructorModifierNotAllowed occurrence selected =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_constructorDiagnostics_iff]
      exact Or.inl ⟨_, selected, rfl⟩
  | fallbackHasParameters occurrence nonempty =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_fallbackDiagnostics_iff]
      exact Or.inr (Or.inl ⟨nonempty, rfl⟩)
  | fallbackHasNonUnitReturn occurrence returnPresent notUnit =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_fallbackDiagnostics_iff]
      exact Or.inr (Or.inr (Or.inl
        ⟨_, returnPresent, notUnit, rfl⟩))
  | signatureParameterTypeMissing occurrence parameterMember missing =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      simp only [nonrecursiveDiagnosticsAt]
      rw [List.mem_append]
      apply Or.inr
      rw [mem_missingParameterTypeDiagnostics_iff]
      exact ⟨_, parameterMember, missing, rfl⟩
  | constructorParameterTypeMissing occurrence parameterMember missing =>
      apply mem_diagnosticCandidates_of_nonrecursiveDiagnosticsAt occurrence
      rw [nonrecursiveDiagnosticsAt, mem_constructorDiagnostics_iff]
      exact Or.inr (Or.inl ⟨_, parameterMember, missing, rfl⟩)
  | breakOutsideLoop occurrence shape =>
      apply mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel_one
        occurrence
      exact breakOutsideLoop_mem_statementDiagnosticsFuel_one shape
  | continueOutsideLoop occurrence shape =>
      apply mem_diagnosticCandidates_of_mem_statementDiagnosticsFuel_one
        occurrence
      exact continueOutsideLoop_mem_statementDiagnosticsFuel_one shape

/-- Executable candidates are exactly the applicable structural diagnostics. -/
@[simp] theorem mem_diagnosticCandidates_iff_applies
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ diagnosticCandidates module ↔
      StructuralDiagnostic.Applies module diagnostic :=
  ⟨mem_diagnosticCandidates_applies, applies_mem_diagnosticCandidates⟩

/-- Canonical diagnostics are exactly the applicable structural diagnostics. -/
@[simp] theorem mem_diagnostics_iff_applies
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic} :
    diagnostic ∈ diagnostics module ↔
      StructuralDiagnostic.Applies module diagnostic := by
  rw [mem_diagnostics, mem_diagnosticCandidates_iff_applies]

/-- Every reported canonical structural diagnostic is declaratively valid. -/
theorem structure_sound
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (member : diagnostic ∈ diagnostics module) :
    StructuralDiagnostic.Applies module diagnostic :=
  mem_diagnostics_iff_applies.mp member

/-- Every declaratively valid structural diagnostic is reported. -/
theorem structure_complete
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (applies : StructuralDiagnostic.Applies module diagnostic) :
    diagnostic ∈ diagnostics module :=
  mem_diagnostics_iff_applies.mpr applies

/-- The module-derived traversal fuel reaches every applicable diagnostic. -/
theorem structuralTraversalFuel_sufficient
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (applies : StructuralDiagnostic.Applies module diagnostic) :
    diagnostic ∈ diagnosticCandidates module :=
  applies_mem_diagnosticCandidates applies

/-- The structural report is duplicate-free, ordered, and extensionally exact. -/
theorem structural_diagnostics_canonical
    (module : ParsedModuleV1) :
    (diagnostics module).Nodup ∧
      (diagnostics module).Pairwise
        (fun left right => StructuralDiagnostic.le left right) ∧
      ∀ diagnostic, diagnostic ∈ diagnostics module ↔
        StructuralDiagnostic.Applies module diagnostic :=
  ⟨diagnostics_nodup module, diagnostics_sorted module,
    fun _ => mem_diagnostics_iff_applies⟩

/-- An empty structural report is exactly declarative module acceptance. -/
@[simp] theorem diagnostics_eq_nil_iff_structurallyAccepts
    (module : ParsedModuleV1) :
    diagnostics module = [] ↔ StructurallyAccepts module := by
  rw [List.eq_nil_iff_forall_not_mem, structurallyAccepts_iff_no_applies]
  simp only [mem_diagnostics_iff_applies]

/-- Executable structural validation succeeds exactly on accepted modules. -/
@[simp] theorem validateStructure_eq_ok_iff_structurallyAccepts
    (module : ParsedModuleV1) :
    validateStructure module = .ok () ↔ StructurallyAccepts module := by
  rw [validateStructure_eq_ok_iff,
    diagnostics_eq_nil_iff_structurallyAccepts]

/-- Every element of a returned error list, and only such an element, applies. -/
theorem mem_validateStructure_error_iff_applies
    {module : ParsedModuleV1}
    {reported : NonemptyList StructuralDiagnostic}
    {diagnostic : StructuralDiagnostic}
    (result : validateStructure module = .error reported) :
    diagnostic ∈ reported.head :: reported.tail ↔
      StructuralDiagnostic.Applies module diagnostic := by
  have exactList :=
    (validateStructure_eq_error_iff module reported).mp result
  rw [← exactList, mem_diagnostics_iff_applies]

/-- A returned structural error list contains no duplicate diagnostics. -/
theorem validateStructure_error_nodup
    {module : ParsedModuleV1}
    {reported : NonemptyList StructuralDiagnostic}
    (result : validateStructure module = .error reported) :
    (reported.head :: reported.tail).Nodup := by
  have exactList :=
    (validateStructure_eq_error_iff module reported).mp result
  rw [← exactList]
  exact diagnostics_nodup module

/-- A returned structural error list follows the canonical diagnostic order. -/
theorem validateStructure_error_sorted
    {module : ParsedModuleV1}
    {reported : NonemptyList StructuralDiagnostic}
    (result : validateStructure module = .error reported) :
    (reported.head :: reported.tail).Pairwise
      (fun left right => StructuralDiagnostic.le left right) := by
  have exactList :=
    (validateStructure_eq_error_iff module reported).mp result
  rw [← exactList]
  exact diagnostics_sorted module

/-- Structural validation returns an error exactly for a rejected module. -/
@[simp] theorem exists_validateStructure_error_iff_not_structurallyAccepts
    (module : ParsedModuleV1) :
    (∃ reported, validateStructure module = .error reported) ↔
      ¬StructurallyAccepts module := by
  constructor
  · rintro ⟨reported, result⟩ accepted
    have success :=
      validateStructure_eq_ok_iff_structurallyAccepts module |>.mpr accepted
    rw [result] at success
    simp at success
  · intro rejected
    cases result : validateStructure module with
    | error reported => exact ⟨reported, rfl⟩
    | ok value =>
        cases value
        exact False.elim (rejected
          (validateStructure_eq_ok_iff_structurallyAccepts module |>.mp result))

end Structure

end Solcore.Surface.Multi
