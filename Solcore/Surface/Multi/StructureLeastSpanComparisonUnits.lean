import Solcore.Surface.Multi.StructureCanonicalOrderingComparisonUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

/-!
Mixed wildcard checks select the least source span with one comparison for
each span after the first.  This module instruments that final validator list
comparison and aggregates its import/export call sites.
-/

/-- One comparison between the current least span and the next candidate. -/
structure LeastSpanComparisonUnit where
  currentLeast : SourceSpan
  candidate : SourceSpan
deriving DecidableEq, Repr

/-- Selected least span and every comparison used to select it. -/
structure LeastSourceSpanRun where
  selected : Option SourceSpan
  comparisons : List LeastSpanComparisonUnit
deriving DecidableEq, Repr

private def leastSourceSpanRunGo
    (least : SourceSpan) : List SourceSpan → LeastSourceSpanRun
  | [] => { selected := some least, comparisons := [] }
  | candidate :: rest =>
      let nextLeast :=
        if sourceSpanBefore candidate least then candidate else least
      let later := leastSourceSpanRunGo nextLeast rest
      { selected := later.selected
        comparisons := { currentLeast := least, candidate } ::
          later.comparisons }

/-- Counted counterpart of `leastSourceSpan?`. -/
def leastSourceSpanRun : List SourceSpan → LeastSourceSpanRun
  | [] => { selected := none, comparisons := [] }
  | first :: rest => leastSourceSpanRunGo first rest

private theorem leastSourceSpanRunGo_selected
    (least : SourceSpan) (rest : List SourceSpan) :
    (leastSourceSpanRunGo least rest).selected =
      some (rest.foldl (fun current candidate =>
        if sourceSpanBefore candidate current then candidate else current)
        least) := by
  induction rest generalizing least with
  | nil => rfl
  | cons candidate rest induction =>
      simp only [leastSourceSpanRunGo, List.foldl_cons]
      split <;> exact induction _

/-- Erasing the trace recovers the validator's exact least-span result. -/
@[simp] theorem leastSourceSpanRun_selected (spans : List SourceSpan) :
    (leastSourceSpanRun spans).selected = leastSourceSpan? spans := by
  cases spans with
  | nil => rfl
  | cons first rest =>
      exact leastSourceSpanRunGo_selected first rest

private theorem leastSourceSpanRunGo_comparisons_length
    (least : SourceSpan) (rest : List SourceSpan) :
    (leastSourceSpanRunGo least rest).comparisons.length = rest.length := by
  induction rest generalizing least with
  | nil => rfl
  | cons candidate rest induction =>
      simp only [leastSourceSpanRunGo, List.length_cons]
      split <;> simp [induction]

/-- Least-span selection performs no more comparisons than it has candidates. -/
theorem leastSourceSpanRun_comparisons_le (spans : List SourceSpan) :
    (leastSourceSpanRun spans).comparisons.length ≤ spans.length := by
  cases spans with
  | nil => simp [leastSourceSpanRun]
  | cons first rest =>
      simp only [leastSourceSpanRun, List.length_cons]
      rw [leastSourceSpanRunGo_comparisons_length]
      omega

/-- Mixed-wildcard diagnostics and the comparisons used by their least-span
selection. -/
structure MixedWildcardRun where
  diagnostics : List StructuralDiagnostic
  comparisons : List LeastSpanComparisonUnit
deriving DecidableEq, Repr

/-- Counted counterpart of `mixedWildcardDiagnostic?`. -/
def mixedWildcardRun
    (entryCount : Nat) (spans : List SourceSpan)
    (makeDiagnostic : SourceSpan → StructuralDiagnostic) : MixedWildcardRun :=
  if entryCount = 1 then
    { diagnostics := [], comparisons := [] }
  else
    let least := leastSourceSpanRun spans
    { diagnostics :=
        match least.selected with
        | none => []
        | some span => [makeDiagnostic span]
      comparisons := least.comparisons }

/-- Erasing the comparison trace recovers the exact mixed-wildcard result. -/
@[simp] theorem mixedWildcardRun_diagnostics
    (entryCount : Nat) (spans : List SourceSpan)
    (makeDiagnostic : SourceSpan → StructuralDiagnostic) :
    (mixedWildcardRun entryCount spans makeDiagnostic).diagnostics =
      mixedWildcardDiagnostic? entryCount spans makeDiagnostic := by
  simp only [mixedWildcardRun, mixedWildcardDiagnostic?]
  split
  · rfl
  · rw [leastSourceSpanRun_selected]
    rfl

theorem mixedWildcardRun_comparisons_le
    (entryCount : Nat) (spans : List SourceSpan)
    (makeDiagnostic : SourceSpan → StructuralDiagnostic) :
    (mixedWildcardRun entryCount spans makeDiagnostic).comparisons.length ≤
      spans.length := by
  simp only [mixedWildcardRun]
  split
  · simp
  · exact leastSourceSpanRun_comparisons_le spans

/-- Closed labels for all mixed-wildcard least-span call sites. -/
inductive StructureLeastSpanComparisonKind where
  | importWildcard
  | exportWildcard
deriving DecidableEq, Repr

/-- One least-span comparison with its validator site and local ordinal. -/
structure StructureLeastSpanComparisonUnit where
  kind : StructureLeastSpanComparisonKind
  siteSpan : SourceSpan
  comparisonOrdinal : Nat
  currentLeast : SourceSpan
  candidate : SourceSpan
deriving DecidableEq, Repr

private def tagLeastSpanComparisons
    (kind : StructureLeastSpanComparisonKind) (siteSpan : SourceSpan)
    (comparisons : List LeastSpanComparisonUnit) :
    List StructureLeastSpanComparisonUnit :=
  comparisons.mapIdx fun comparisonOrdinal comparison => {
    kind
    siteSpan
    comparisonOrdinal
    currentLeast := comparison.currentLeast
    candidate := comparison.candidate
  }

/-- Least-span comparisons in one import selection. -/
def importSelectionLeastSpanComparisonTrace
    (selection : ImportSelection) :
    List StructureLeastSpanComparisonUnit :=
  let entries := selection.payload.entries
  let spans := entries.filterMap importWildcardSpan?
  tagLeastSpanComparisons .importWildcard selection.span
    (mixedWildcardRun entries.length spans
      StructuralDiagnostic.mixedImportWildcard).comparisons

private def localExportWildcardSpans
    (entries : List ExportEntry) : List SourceSpan :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard marker => some marker.span
    | .item _ | .allFrom _ _ => none

/-- Least-span comparisons in one local export selection. -/
def localExportLeastSpanComparisonTrace
    (selection : LocalExportList) :
    List StructureLeastSpanComparisonUnit :=
  let entries := selection.payload.entries
  let spans := localExportWildcardSpans entries
  tagLeastSpanComparisons .exportWildcard selection.span
    (mixedWildcardRun entries.length spans
      StructuralDiagnostic.mixedExportWildcard).comparisons

private def remoteExportWildcardSpans
    (entries : List RemoteExportEntry) : List SourceSpan :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard marker => some marker.span
    | .item _ => none

/-- Least-span comparisons in one remote export selection. -/
def remoteExportLeastSpanComparisonTrace
    (selection : RemoteExportSelection) :
    List StructureLeastSpanComparisonUnit :=
  match selection.payload with
  | .dotWildcard _ => []
  | .braced entries =>
      let spans := remoteExportWildcardSpans entries
      tagLeastSpanComparisons .exportWildcard selection.span
        (mixedWildcardRun entries.length spans
          StructuralDiagnostic.mixedExportWildcard).comparisons

/-- Least-span comparisons reached from one top-level item. -/
def topItemLeastSpanComparisonTrace
    (item : TopItem) : List StructureLeastSpanComparisonUnit :=
  match item.payload with
  | .importDecl declaration =>
      match declaration.payload.mode with
      | .module _ => []
      | .items selection _ =>
          importSelectionLeastSpanComparisonTrace selection
  | .exportDecl declaration =>
      match declaration.payload with
      | .module _ _ => []
      | .local selection => localExportLeastSpanComparisonTrace selection
      | .from _ selection => remoteExportLeastSpanComparisonTrace selection
  | .pragmaDecl _ | .dataDecl _ | .typeAliasDecl _ | .classDecl _ |
      .instanceDecl _ | .contractDecl _ | .functionDecl _ => []

/-- Complete least-span comparison trace for a parsed module. -/
def structureLeastSpanComparisonTrace
    (module : ParsedModuleV1) : List StructureLeastSpanComparisonUnit :=
  module.payload.items.flatMap topItemLeastSpanComparisonTrace

/-- Number of mixed-wildcard least-span comparisons for a module. -/
def structureLeastSpanComparisonUnits (module : ParsedModuleV1) : Nat :=
  (structureLeastSpanComparisonTrace module).length

end Structure

end Solcore.Surface.Multi
