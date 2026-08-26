import Solcore.Surface.Multi.StructureLeastSpanComparisonUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

private theorem length_le_measureList_of_one_le
    {alpha : Type} (measure : alpha → Nat)
    (oneLe : ∀ value, 1 ≤ measure value)
    (values : List alpha) :
    values.length ≤ measureList measure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      simpa [measureList, Nat.add_comm] using
        Nat.add_le_add (oneLe head) induction

private theorem importSelectorEntryMeasure_one_le
    (entry : ImportSelectorEntry) :
    1 ≤ importSelectorEntryMeasure entry := by
  cases entry with
  | mk span payload =>
      cases payload <;> simp only [importSelectorEntryMeasure] <;> omega

private theorem exportEntryMeasure_one_le (entry : ExportEntry) :
    1 ≤ exportEntryMeasure entry := by
  cases entry with
  | mk span payload =>
      cases payload <;> simp only [exportEntryMeasure] <;> omega

private theorem remoteExportEntryMeasure_one_le
    (entry : RemoteExportEntry) :
    1 ≤ remoteExportEntryMeasure entry := by
  cases entry with
  | mk span payload =>
      cases payload <;> simp only [remoteExportEntryMeasure] <;> omega

/-- The least-span comparisons at one import selection fit within that
selection's concrete AST measure. -/
theorem importSelectionLeastSpanComparisonTrace_length_le_measure
    (selection : ImportSelection) :
    (importSelectionLeastSpanComparisonTrace selection).length ≤
      importSelectionMeasure selection := by
  have comparisonBound :
      (importSelectionLeastSpanComparisonTrace selection).length ≤
        selection.payload.entries.length := by
    change
      (List.mapIdx _
        (mixedWildcardRun selection.payload.entries.length
          (selection.payload.entries.filterMap importWildcardSpan?)
          StructuralDiagnostic.mixedImportWildcard).comparisons).length ≤ _
    rw [List.length_mapIdx]
    exact Nat.le_trans
      (mixedWildcardRun_comparisons_le
        selection.payload.entries.length
        (selection.payload.entries.filterMap importWildcardSpan?)
        StructuralDiagnostic.mixedImportWildcard)
      (List.length_filterMap_le importWildcardSpan?
        selection.payload.entries)
  have entriesBound :
      selection.payload.entries.length ≤
        measureList importSelectorEntryMeasure selection.payload.entries :=
    length_le_measureList_of_one_le
      importSelectorEntryMeasure importSelectorEntryMeasure_one_le _
  simp only [importSelectionMeasure]
  omega

/-- The least-span comparisons at one local export selection fit within that
selection's concrete AST measure. -/
theorem localExportLeastSpanComparisonTrace_length_le_measure
    (selection : LocalExportList) :
    (localExportLeastSpanComparisonTrace selection).length ≤
      localExportListMeasure selection := by
  have comparisonBound :
      (localExportLeastSpanComparisonTrace selection).length ≤
        selection.payload.entries.length := by
    change
      (List.mapIdx _
        (mixedWildcardRun selection.payload.entries.length
          (selection.payload.entries.filterMap fun entry =>
            match entry.payload with
            | .wildcard marker => some marker.span
            | .item _ | .allFrom _ _ => none)
          StructuralDiagnostic.mixedExportWildcard).comparisons).length ≤ _
    rw [List.length_mapIdx]
    exact Nat.le_trans
      (mixedWildcardRun_comparisons_le
        selection.payload.entries.length
        (selection.payload.entries.filterMap fun entry =>
          match entry.payload with
          | .wildcard marker => some marker.span
          | .item _ | .allFrom _ _ => none)
        StructuralDiagnostic.mixedExportWildcard)
      (List.length_filterMap_le
        (fun entry =>
          match entry.payload with
          | .wildcard marker => some marker.span
          | .item _ | .allFrom _ _ => none)
        selection.payload.entries)
  have entriesBound :
      selection.payload.entries.length ≤
        measureList exportEntryMeasure selection.payload.entries :=
    length_le_measureList_of_one_le
      exportEntryMeasure exportEntryMeasure_one_le _
  simp only [localExportListMeasure]
  omega

/-- The least-span comparisons at one remote export selection fit within that
selection's concrete AST measure. -/
theorem remoteExportLeastSpanComparisonTrace_length_le_measure
    (selection : RemoteExportSelection) :
    (remoteExportLeastSpanComparisonTrace selection).length ≤
      remoteExportSelectionMeasure selection := by
  cases selection with
  | mk span payload =>
      cases payload with
      | dotWildcard marker =>
          simp [remoteExportLeastSpanComparisonTrace,
            remoteExportSelectionMeasure]
      | braced entries =>
          have comparisonBound :
              (remoteExportLeastSpanComparisonTrace ⟨span, .braced entries⟩).length ≤
                entries.length := by
            change
              (List.mapIdx _
                (mixedWildcardRun entries.length
                  (entries.filterMap fun entry =>
                    match entry.payload with
                    | .wildcard marker => some marker.span
                    | .item _ => none)
                  StructuralDiagnostic.mixedExportWildcard).comparisons).length ≤ _
            rw [List.length_mapIdx]
            exact Nat.le_trans
              (mixedWildcardRun_comparisons_le
                entries.length
                (entries.filterMap fun entry =>
                  match entry.payload with
                  | .wildcard marker => some marker.span
                  | .item _ => none)
                StructuralDiagnostic.mixedExportWildcard)
              (List.length_filterMap_le
                (fun entry =>
                  match entry.payload with
                  | .wildcard marker => some marker.span
                  | .item _ => none)
                entries)
          have entriesBound :
              entries.length ≤ measureList remoteExportEntryMeasure entries :=
            length_le_measureList_of_one_le
              remoteExportEntryMeasure remoteExportEntryMeasure_one_le _
          simp only [remoteExportSelectionMeasure]
          omega

/-- Least-span comparisons rooted at one top-level item fit within that item's
concrete AST measure. -/
theorem topItemLeastSpanComparisonTrace_length_le_measure
    (item : TopItem) :
    (topItemLeastSpanComparisonTrace item).length ≤ topItemMeasure item := by
  cases item with
  | mk span payload =>
      cases payload with
      | importDecl declaration =>
          cases declaration with
          | mk declarationSpan declarationPayload =>
              cases declarationPayload with
              | mk moduleRef mode =>
                  cases mode with
                  | module alias =>
                      simp [topItemLeastSpanComparisonTrace, topItemMeasure]
                  | items selection hidingClause =>
                      have selectionBound :=
                        importSelectionLeastSpanComparisonTrace_length_le_measure
                          selection
                      simp only [topItemLeastSpanComparisonTrace,
                        topItemMeasure, importDeclMeasure, importModeMeasure]
                      omega
      | exportDecl declaration =>
          cases declaration with
          | mk declarationSpan mode =>
              cases mode with
              | «local» selection =>
                  have selectionBound :=
                    localExportLeastSpanComparisonTrace_length_le_measure
                      selection
                  simp only [topItemLeastSpanComparisonTrace,
                    topItemMeasure, exportModeMeasure]
                  omega
              | module moduleRef alias =>
                  simp [topItemLeastSpanComparisonTrace, topItemMeasure]
              | «from» moduleRef selection =>
                  have selectionBound :=
                    remoteExportLeastSpanComparisonTrace_length_le_measure
                      selection
                  simp only [topItemLeastSpanComparisonTrace,
                    topItemMeasure, exportModeMeasure]
                  omega
      | pragmaDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | dataDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | typeAliasDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | classDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | instanceDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | contractDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]
      | functionDecl declaration =>
          simp [topItemLeastSpanComparisonTrace, topItemMeasure]

private theorem topItemLeastSpanComparisonTrace_flatMap_length_le_measureList
    (items : List TopItem) :
    (items.flatMap topItemLeastSpanComparisonTrace).length ≤
      measureList topItemMeasure items := by
  induction items with
  | nil => simp [measureList]
  | cons head tail induction =>
      have headBound :=
        topItemLeastSpanComparisonTrace_length_le_measure head
      simpa [measureList] using Nat.add_le_add headBound induction

/-- All least-span comparisons performed for a module are bounded by the
module's concrete AST-node count. -/
theorem structureLeastSpanComparisonUnits_le_astNodeMeasure
    (module : ParsedModuleV1) :
    structureLeastSpanComparisonUnits module ≤ astNodeMeasure module := by
  have traceBound :=
    topItemLeastSpanComparisonTrace_flatMap_length_le_measureList
      module.payload.items
  simp only [structureLeastSpanComparisonUnits,
    structureLeastSpanComparisonTrace, astNodeMeasure]
  omega

end Structure

end Solcore.Surface.Multi
