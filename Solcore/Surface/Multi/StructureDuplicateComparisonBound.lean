import Solcore.Surface.Multi.StructureDuplicateComparisonUnits

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

private theorem measureList_filterMap_le
    {alpha beta : Type}
    (sourceMeasure : alpha → Nat) (targetMeasure : beta → Nat)
    (project : alpha → Option beta)
    (projected : ∀ source target,
      project source = some target →
        targetMeasure target ≤ sourceMeasure source)
    (values : List alpha) :
    measureList targetMeasure (values.filterMap project) ≤
      measureList sourceMeasure values := by
  induction values with
  | nil => simp [measureList]
  | cons head tail induction =>
      simp only [List.filterMap_cons, measureList, List.map_cons,
        List.sum_cons]
      cases equation : project head with
      | none =>
          simp only
          exact Nat.le_trans induction (Nat.le_add_left _ _)
      | some target =>
          simp only
          exact Nat.add_le_add (projected head target equation) induction

private theorem square_add_square_le_add_square (left right : Nat) :
    left * left + right * right ≤
      (left + right) * (left + right) := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  omega

private theorem square_le_square {left right : Nat}
    (less : left ≤ right) :
    left * left ≤ right * right :=
  Nat.mul_le_mul less less

private theorem importSelectorEntryMeasure_one_le
    (entry : ImportSelectorEntry) :
    1 ≤ importSelectorEntryMeasure entry := by
  cases entry with
  | mk span payload =>
      cases payload <;> simp only [importSelectorEntryMeasure] <;> omega

private theorem identifierMeasure_one_le
    (identifier : IdentifierOccurrence) :
    1 ≤ identifierMeasure identifier := by
  simp [identifierMeasure]

private theorem namedImportEntries_length_le_entries
    (entries : List ImportSelectorEntry) :
    (namedImportEntries entries).length ≤ entries.length := by
  exact List.length_filterMap_le _ _

/-- Both duplicate-name scans at one import selection fit within twice the
square of that selection's concrete AST measure. -/
theorem importSelectionDuplicateComparisonTrace_length_le_two_measure_square
    (selection : ImportSelection) :
    (importSelectionDuplicateComparisonTrace selection).length ≤
      2 * (importSelectionMeasure selection *
        importSelectionMeasure selection) := by
  let named := namedImportEntries selection.payload.entries
  have namedEntries : named.length ≤ selection.payload.entries.length :=
    namedImportEntries_length_le_entries selection.payload.entries
  have entriesMeasure :
      selection.payload.entries.length ≤
        measureList importSelectorEntryMeasure
          selection.payload.entries :=
    length_le_measureList_of_one_le importSelectorEntryMeasure
      importSelectorEntryMeasure_one_le _
  have namedMeasure : named.length ≤ importSelectionMeasure selection := by
    simp only [importSelectionMeasure]
    omega
  have sourceBound := duplicateComparisonTrace_length_le_square
    .importSourceName selection.span
    (fun entry : IdentifierOccurrence × IdentifierOccurrence =>
      entry.1.payload)
    (fun entry => .duplicateImportSourceName entry.1.span entry.1.payload)
    named
  have localBound := duplicateComparisonTrace_length_le_square
    .importLocalName selection.span
    (fun entry : IdentifierOccurrence × IdentifierOccurrence =>
      entry.2.payload)
    (fun entry => .duplicateImportLocalName entry.2.span entry.2.payload)
    named
  have namedSquare := square_le_square namedMeasure
  simp only [named] at sourceBound localBound namedSquare
  simp only [importSelectionDuplicateComparisonTrace, List.length_append]
  omega

/-- Duplicate-name comparisons in one hiding clause fit within the square of
that clause's concrete AST measure. -/
theorem hidingDuplicateComparisonTrace_length_le_measure_square
    (clause : HidingClause) :
    (hidingDuplicateComparisonTrace clause).length ≤
      hidingClauseMeasure clause * hidingClauseMeasure clause := by
  have namesMeasure :
      clause.payload.names.length ≤ hidingClauseMeasure clause := by
    have namesBound := length_le_measureList_of_one_le identifierMeasure
      identifierMeasure_one_le clause.payload.names
    simp only [hidingClauseMeasure]
    omega
  have traceBound := duplicateComparisonTrace_length_le_square
    .hiddenName clause.span
    (fun name : IdentifierOccurrence => name.payload)
    (fun name => .duplicateHiddenName name.span name.payload)
    clause.payload.names
  exact Nat.le_trans traceBound (square_le_square namesMeasure)

private theorem nonemptyIdentifierLength_le_measure
    (identifiers : NonemptyList IdentifierOccurrence) :
    (nonemptyToList identifiers).length ≤
      measureNonemptyList identifierMeasure identifiers := by
  cases identifiers with
  | mk head tail =>
      have tailBound := length_le_measureList_of_one_le identifierMeasure
        identifierMeasure_one_le tail
      simp only [nonemptyToList, List.length_cons, measureNonemptyList]
      have headBound := identifierMeasure_one_le head
      omega

/-- Constructor-name comparisons fit within the square of the optional
constructor selection's concrete measure. -/
theorem constructorSelectionDuplicateComparisonTrace_length_le_measure_square
    (selection : Option ConstructorSelection) :
    (constructorSelectionDuplicateComparisonTrace selection).length ≤
      measureOption constructorSelectionMeasure selection *
        measureOption constructorSelectionMeasure selection := by
  cases selection with
  | none => simp [constructorSelectionDuplicateComparisonTrace, measureOption]
  | some located =>
      cases located with
      | mk span payload =>
          cases payload with
          | all marker =>
              simp [constructorSelectionDuplicateComparisonTrace,
                measureOption]
          | named constructors =>
              have lengthMeasure :
                  (nonemptyToList constructors).length ≤
                    constructorSelectionMeasure ⟨span, .named constructors⟩ := by
                have namesBound :=
                  nonemptyIdentifierLength_le_measure constructors
                simp only [constructorSelectionMeasure]
                omega
              have traceBound := duplicateComparisonTrace_length_le_square
                .exportConstructor span
                (fun name : IdentifierOccurrence => name.payload)
                (fun name =>
                  .duplicateExportConstructor name.span name.payload)
                (nonemptyToList constructors)
              simp only [measureOption]
              exact Nat.le_trans traceBound (square_le_square lengthMeasure)

/-- Nested constructor comparisons in one export item fit within the square
of the item's concrete AST measure. -/
theorem exportItemDuplicateComparisonTrace_length_le_measure_square
    (item : ExportItem) :
    (exportItemDuplicateComparisonTrace item).length ≤
      exportItemMeasure item * exportItemMeasure item := by
  have nested :=
    constructorSelectionDuplicateComparisonTrace_length_le_measure_square
      item.payload.constructors
  have optionLe :
      measureOption constructorSelectionMeasure item.payload.constructors ≤
        exportItemMeasure item := by
    simp only [exportItemMeasure]
    omega
  exact Nat.le_trans nested (square_le_square optionLe)

private theorem exportItemsDuplicateComparisonTrace_length_le_measure_square
    (items : List ExportItem) :
    (items.flatMap exportItemDuplicateComparisonTrace).length ≤
      measureList exportItemMeasure items *
        measureList exportItemMeasure items := by
  induction items with
  | nil => simp [measureList]
  | cons head tail induction =>
      have headBound :=
        exportItemDuplicateComparisonTrace_length_le_measure_square head
      simp only [List.flatMap_cons, List.length_append, measureList,
        List.map_cons, List.sum_cons]
      exact Nat.le_trans (Nat.add_le_add headBound induction)
        (square_add_square_le_add_square _ _)

private theorem localExportItems_measure_le_entries
    (entries : List ExportEntry) :
    measureList exportItemMeasure
        (localExportItemsForDuplicateComparisons entries) ≤
      measureList exportEntryMeasure entries := by
  apply measureList_filterMap_le exportEntryMeasure exportItemMeasure
  intro source target projected
  cases source with
  | mk span payload =>
      cases payload with
      | wildcard marker => simp at projected
      | item item =>
          simp only at projected
          cases projected
          simp [exportEntryMeasure]
      | allFrom reference marker => simp at projected

private theorem remoteExportItems_measure_le_entries
    (entries : List RemoteExportEntry) :
    measureList exportItemMeasure
        (remoteExportItemsForDuplicateComparisons entries) ≤
      measureList remoteExportEntryMeasure entries := by
  apply measureList_filterMap_le remoteExportEntryMeasure exportItemMeasure
  intro source target projected
  cases source with
  | mk span payload =>
      cases payload with
      | wildcard marker => simp at projected
      | item item =>
          simp only at projected
          cases projected
          simp [remoteExportEntryMeasure]

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

/-- All duplicate comparisons in one local export list fit within three times
the square of that list's concrete AST measure. -/
theorem localExportDuplicateComparisonTrace_length_le_three_measure_square
    (selection : LocalExportList) :
    (localExportDuplicateComparisonTrace selection).length ≤
      3 * (localExportListMeasure selection *
        localExportListMeasure selection) := by
  let entries := selection.payload.entries
  let items := localExportItemsForDuplicateComparisons entries
  let references := localExportReferencesForDuplicateComparisons entries
  have itemLength : items.length ≤ localExportListMeasure selection := by
    have entriesBound := length_le_measureList_of_one_le exportEntryMeasure
      exportEntryMeasure_one_le entries
    calc
      items.length ≤ entries.length := by
        dsimp only [items, entries,
          localExportItemsForDuplicateComparisons]
        exact List.length_filterMap_le _ _
      _ ≤ measureList exportEntryMeasure entries := entriesBound
      _ ≤ localExportListMeasure selection := by
        simp only [entries, localExportListMeasure]
        omega
  have referenceLength :
      references.length ≤ localExportListMeasure selection := by
    have entriesBound := length_le_measureList_of_one_le exportEntryMeasure
      exportEntryMeasure_one_le entries
    calc
      references.length ≤ entries.length := by
        dsimp only [references, entries,
          localExportReferencesForDuplicateComparisons]
        exact List.length_filterMap_le _ _
      _ ≤ measureList exportEntryMeasure entries := entriesBound
      _ ≤ localExportListMeasure selection := by
        simp only [entries, localExportListMeasure]
        omega
  have itemTraceBound := duplicateComparisonTrace_length_le_square
    .exportName selection.span
    (fun item : ExportItem => item.payload.name.payload)
    (fun item => .duplicateExportName
      item.payload.name.span item.payload.name.payload)
    items
  have referenceTraceBound := duplicateComparisonTrace_length_le_square
    .exportModuleReference selection.span ModuleReference.eraseLocations
    (fun reference => .duplicateExportModuleReference
      reference.span reference.eraseLocations)
    references
  have constructorTraceBound :=
    exportItemsDuplicateComparisonTrace_length_le_measure_square items
  have itemMeasures :
      measureList exportItemMeasure items ≤
        localExportListMeasure selection := by
    have filtered := localExportItems_measure_le_entries entries
    simp only [items, entries] at filtered ⊢
    simp only [localExportListMeasure]
    omega
  have itemSquare := square_le_square itemLength
  have referenceSquare := square_le_square referenceLength
  have constructorSquare := square_le_square itemMeasures
  dsimp only [entries, items] at itemTraceBound constructorTraceBound itemSquare constructorSquare
  dsimp only [entries, references] at referenceTraceBound referenceSquare
  simp only [localExportDuplicateComparisonTrace, List.length_append]
  omega

/-- All duplicate comparisons in one remote export selection fit within three
times the square of that selection's concrete AST measure. -/
theorem remoteExportDuplicateComparisonTrace_length_le_three_measure_square
    (selection : RemoteExportSelection) :
    (remoteExportDuplicateComparisonTrace selection).length ≤
      3 * (remoteExportSelectionMeasure selection *
        remoteExportSelectionMeasure selection) := by
  cases selection with
  | mk span payload =>
      cases payload with
      | dotWildcard marker =>
          simp [remoteExportDuplicateComparisonTrace,
            remoteExportSelectionMeasure]
      | braced entries =>
          let items := remoteExportItemsForDuplicateComparisons entries
          have itemLength :
              items.length ≤
                remoteExportSelectionMeasure ⟨span, .braced entries⟩ := by
            have entriesBound := length_le_measureList_of_one_le
              remoteExportEntryMeasure remoteExportEntryMeasure_one_le entries
            calc
              items.length ≤ entries.length := by
                dsimp only [items,
                  remoteExportItemsForDuplicateComparisons]
                exact List.length_filterMap_le _ _
              _ ≤ measureList remoteExportEntryMeasure entries :=
                entriesBound
              _ ≤
                  remoteExportSelectionMeasure ⟨span, .braced entries⟩ := by
                simp only [remoteExportSelectionMeasure]
                omega
          have itemTraceBound := duplicateComparisonTrace_length_le_square
            .exportName span
            (fun item : ExportItem => item.payload.name.payload)
            (fun item => .duplicateExportName
              item.payload.name.span item.payload.name.payload)
            items
          have constructorTraceBound :=
            exportItemsDuplicateComparisonTrace_length_le_measure_square items
          have itemMeasures :
              measureList exportItemMeasure items ≤
                remoteExportSelectionMeasure ⟨span, .braced entries⟩ := by
            have filtered := remoteExportItems_measure_le_entries entries
            simp only [items] at filtered ⊢
            simp only [remoteExportSelectionMeasure]
            omega
          have itemSquare := square_le_square itemLength
          have constructorSquare := square_le_square itemMeasures
          dsimp only [items] at itemTraceBound constructorTraceBound itemSquare constructorSquare
          simp only [remoteExportDuplicateComparisonTrace,
            List.length_append]
          omega

/-- Duplicate-target comparisons in one pragma fit within the square of that
declaration's concrete AST measure. -/
theorem pragmaDuplicateComparisonTrace_length_le_measure_square
    (declaration : PragmaDecl) :
    (pragmaDuplicateComparisonTrace declaration).length ≤
      pragmaDeclMeasure declaration * pragmaDeclMeasure declaration := by
  have targetsMeasure :
      declaration.payload.targets.length ≤
        pragmaDeclMeasure declaration := by
    have targetsBound := length_le_measureList_of_one_le identifierMeasure
      identifierMeasure_one_le declaration.payload.targets
    simp only [pragmaDeclMeasure]
    omega
  have traceBound := duplicateComparisonTrace_length_le_square
    .pragmaTarget declaration.span
    (fun target : IdentifierOccurrence => target.payload)
    (fun target => .duplicatePragmaTarget target.span target.payload)
    declaration.payload.targets
  exact Nat.le_trans traceBound (square_le_square targetsMeasure)

/-- Duplicate comparisons rooted at one top-level item fit within three times
the square of that item's concrete AST measure. -/
theorem topItemDuplicateComparisonTrace_length_le_three_measure_square
    (item : TopItem) :
    (topItemDuplicateComparisonTrace item).length ≤
      3 * (topItemMeasure item * topItemMeasure item) := by
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
                      simp [topItemDuplicateComparisonTrace, topItemMeasure]
                  | items selection hidingClause =>
                      have selectionBound :=
                        importSelectionDuplicateComparisonTrace_length_le_two_measure_square
                          selection
                      have selectionMeasure :
                          importSelectionMeasure selection ≤
                            topItemMeasure
                              ⟨span, .importDecl
                                ⟨declarationSpan,
                                  ⟨moduleRef, .items selection hidingClause⟩⟩⟩ := by
                        simp only [topItemMeasure, importDeclMeasure,
                          importModeMeasure]
                        omega
                      have selectionSquare := square_le_square selectionMeasure
                      cases hidingClause with
                      | none =>
                          simp only [topItemDuplicateComparisonTrace,
                            List.length_append, List.length_nil,
                            Nat.add_zero]
                          omega
                      | some clause =>
                          have hidingBound :=
                            hidingDuplicateComparisonTrace_length_le_measure_square
                              clause
                          have hidingMeasure :
                              hidingClauseMeasure clause ≤
                                topItemMeasure
                                  ⟨span, .importDecl
                                    ⟨declarationSpan,
                                      ⟨moduleRef,
                                        .items selection (some clause)⟩⟩⟩ := by
                            simp only [topItemMeasure, importDeclMeasure,
                              importModeMeasure, measureOption]
                            omega
                          have hidingSquare := square_le_square hidingMeasure
                          simp only [topItemDuplicateComparisonTrace,
                            List.length_append]
                          omega
      | exportDecl declaration =>
          cases declaration with
          | mk declarationSpan mode =>
              cases mode with
              | «local» selection =>
                  have localBound :=
                    localExportDuplicateComparisonTrace_length_le_three_measure_square
                      selection
                  have measureBound :
                      localExportListMeasure selection ≤
                        topItemMeasure
                          ⟨span, .exportDecl
                            ⟨declarationSpan, .local selection⟩⟩ := by
                    simp only [topItemMeasure, exportModeMeasure]
                    omega
                  have squareBound := square_le_square measureBound
                  simp only [topItemDuplicateComparisonTrace]
                  omega
              | module moduleRef alias =>
                  simp [topItemDuplicateComparisonTrace, topItemMeasure]
              | «from» moduleRef selection =>
                  have remoteBound :=
                    remoteExportDuplicateComparisonTrace_length_le_three_measure_square
                      selection
                  have measureBound :
                      remoteExportSelectionMeasure selection ≤
                        topItemMeasure
                          ⟨span, .exportDecl
                            ⟨declarationSpan, .from moduleRef selection⟩⟩ := by
                    simp only [topItemMeasure, exportModeMeasure]
                    omega
                  have squareBound := square_le_square measureBound
                  simp only [topItemDuplicateComparisonTrace]
                  omega
      | pragmaDecl declaration =>
          have pragmaBound :=
            pragmaDuplicateComparisonTrace_length_le_measure_square declaration
          have measureBound :
              pragmaDeclMeasure declaration ≤
                topItemMeasure ⟨span, .pragmaDecl declaration⟩ := by
            simp only [topItemMeasure]
            omega
          have squareBound := square_le_square measureBound
          simp only [topItemDuplicateComparisonTrace]
          omega
      | dataDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]
      | typeAliasDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]
      | classDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]
      | instanceDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]
      | contractDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]
      | functionDecl declaration =>
          simp [topItemDuplicateComparisonTrace, topItemMeasure]

private theorem topItemDuplicateComparisonTrace_flatMap_length_le_three_square
    (items : List TopItem) :
    (items.flatMap topItemDuplicateComparisonTrace).length ≤
      3 * (measureList topItemMeasure items *
        measureList topItemMeasure items) := by
  induction items with
  | nil => simp [measureList]
  | cons head tail induction =>
      have headBound :=
        topItemDuplicateComparisonTrace_length_le_three_measure_square head
      have squares := square_add_square_le_add_square
        (topItemMeasure head) (measureList topItemMeasure tail)
      rw [List.flatMap_cons, List.length_append]
      change _ ≤
        3 * ((topItemMeasure head + measureList topItemMeasure tail) *
          (topItemMeasure head + measureList topItemMeasure tail))
      calc
        _ ≤
            3 * (topItemMeasure head * topItemMeasure head) +
              3 * (measureList topItemMeasure tail *
                measureList topItemMeasure tail) :=
          Nat.add_le_add headBound induction
        _ = 3 * (topItemMeasure head * topItemMeasure head +
              measureList topItemMeasure tail *
                measureList topItemMeasure tail) := by
          rw [Nat.mul_add]
        _ ≤ _ := Nat.mul_le_mul_left 3 squares

/-- The complete module duplicate-comparison count is at most three times the
square of its concrete AST-node count. -/
theorem structureDuplicateComparisonUnits_le_three_astNodeMeasure_square
    (module : ParsedModuleV1) :
    structureDuplicateComparisonUnits module ≤
      3 * (astNodeMeasure module * astNodeMeasure module) := by
  have traceBound :=
    topItemDuplicateComparisonTrace_flatMap_length_le_three_square
      module.payload.items
  have measureBound :
      measureList topItemMeasure module.payload.items ≤
        astNodeMeasure module := by
    simp only [astNodeMeasure]
    omega
  have squareBound := square_le_square measureBound
  simp only [structureDuplicateComparisonUnits,
    structureDuplicateComparisonTrace] at ⊢ traceBound
  exact Nat.le_trans traceBound (Nat.mul_le_mul_left 3 squareBound)

end Structure

end Solcore.Surface.Multi
