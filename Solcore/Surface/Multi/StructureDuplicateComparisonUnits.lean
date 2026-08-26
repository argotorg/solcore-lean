import Solcore.Surface.Multi.StructureNodeVisitUnits
import Solcore.Surface.Multi.Structure

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

/-!
`duplicateDiagnostics` performs one key comparison for each visited member of
its accumulated `seen` list.  This module makes those comparison units
executable without changing the validator.  The counted runner below follows
the same branches as `duplicateDiagnostics.go`, and its value projection is
proved equal to that helper.

Canonical diagnostic deduplication and ordering have their own comparisons;
they are deliberately outside this focused accounting slice.
-/

/-- One equality comparison made while checking a candidate against keys
seen earlier in the same duplicate-diagnostic invocation. -/
structure DuplicateComparisonUnit where
  candidateOrdinal : Nat
  seenOffset : Nat
deriving DecidableEq, Repr

/-- The offsets visited by the list-membership decision.  The trace stops at
the first equal key, exactly as the executable membership test does. -/
def membershipComparisonOffsets {κ : Type} [DecidableEq κ]
    (keyValue : κ) : List κ → List Nat
  | [] => []
  | head :: tail =>
      0 :: if keyValue = head then []
      else (membershipComparisonOffsets keyValue tail).map Nat.succ

/-- Diagnostics and comparison events from one duplicate-diagnostic run. -/
structure DuplicateDiagnosticsRun where
  diagnostics : List StructuralDiagnostic
  comparisons : List DuplicateComparisonUnit
deriving Repr

/-- Counted counterpart of `duplicateDiagnostics.go`. -/
def duplicateDiagnosticsRunGo {α κ : Type} [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (seen : List κ) (candidateOrdinal : Nat) :
    List α → DuplicateDiagnosticsRun
  | [] => { diagnostics := [], comparisons := [] }
  | value :: rest =>
      let keyValue := key value
      let currentComparisons :=
        (membershipComparisonOffsets keyValue seen).map fun seenOffset =>
          { candidateOrdinal, seenOffset }
      let later := duplicateDiagnosticsRunGo key makeDiagnostic
        (keyValue :: seen) (candidateOrdinal + 1) rest
      { diagnostics :=
          if keyValue ∈ seen then makeDiagnostic value :: later.diagnostics
          else later.diagnostics
        comparisons := currentComparisons ++ later.comparisons }

/-- Counted execution of the validator's public duplicate helper. -/
def duplicateDiagnosticsRun {α κ : Type} [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α) : DuplicateDiagnosticsRun :=
  duplicateDiagnosticsRunGo key makeDiagnostic [] 0 values

/-- Executable number of equality comparisons made by a duplicate check. -/
def duplicateComparisonUnits {α κ : Type} [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α) : Nat :=
  (duplicateDiagnosticsRun key makeDiagnostic values).comparisons.length

@[simp] theorem duplicateDiagnosticsRunGo_diagnostics {α κ : Type}
    [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (seen : List κ) (candidateOrdinal : Nat) (values : List α) :
    (duplicateDiagnosticsRunGo key makeDiagnostic seen candidateOrdinal values).diagnostics =
      duplicateDiagnostics.go key makeDiagnostic seen values := by
  induction values generalizing seen candidateOrdinal with
  | nil => rfl
  | cons value rest induction =>
      simp only [duplicateDiagnosticsRunGo, duplicateDiagnostics.go]
      rw [induction]

/-- Erasing the comparison trace recovers the validator's duplicate result. -/
@[simp] theorem duplicateDiagnosticsRun_diagnostics {α κ : Type}
    [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α) :
    (duplicateDiagnosticsRun key makeDiagnostic values).diagnostics =
      duplicateDiagnostics key makeDiagnostic values := by
  exact duplicateDiagnosticsRunGo_diagnostics
    key makeDiagnostic [] 0 values

theorem membershipComparisonOffsets_length_le {κ : Type}
    [DecidableEq κ] (keyValue : κ) (values : List κ) :
    (membershipComparisonOffsets keyValue values).length ≤ values.length := by
  induction values with
  | nil => simp [membershipComparisonOffsets]
  | cons head tail induction =>
      simp only [membershipComparisonOffsets]
      split
      · simp
      · simp only [List.length_cons, List.length_map]
        omega

theorem duplicateDiagnosticsRunGo_comparisons_length_le {α κ : Type}
    [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (seen : List κ) (candidateOrdinal : Nat) (values : List α) :
    (duplicateDiagnosticsRunGo key makeDiagnostic seen candidateOrdinal values).comparisons.length ≤
      values.length * (seen.length + values.length) := by
  induction values generalizing seen candidateOrdinal with
  | nil => simp [duplicateDiagnosticsRunGo]
  | cons value rest induction =>
      simp only [duplicateDiagnosticsRunGo, List.length_append, List.length_map]
      have currentBound :=
        membershipComparisonOffsets_length_le (key value) seen
      have laterBound := induction
        (seen := key value :: seen) (candidateOrdinal := candidateOrdinal + 1)
      simp only [List.length_cons] at laterBound ⊢
      apply Nat.le_trans (Nat.add_le_add currentBound laterBound)
      let total := seen.length + (rest.length + 1)
      have inner : seen.length + 1 + rest.length = total := by
        simp only [total]
        omega
      have seenLe : seen.length ≤ total := by
        simp only [total]
        omega
      rw [inner]
      calc
        seen.length + rest.length * total =
            rest.length * total + seen.length := Nat.add_comm _ _
        _ ≤ rest.length * total + total :=
          Nat.add_le_add_left seenLe _
        _ = (rest.length + 1) * total := by
          simp [Nat.add_mul]

/-- One duplicate-helper invocation uses at most the square of its input
length many key comparisons. -/
theorem duplicateComparisonUnits_le_square {α κ : Type}
    [DecidableEq κ]
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α) :
    duplicateComparisonUnits key makeDiagnostic values ≤
      values.length * values.length := by
  simpa [duplicateComparisonUnits, duplicateDiagnosticsRun] using
    duplicateDiagnosticsRunGo_comparisons_length_le
      key makeDiagnostic [] 0 values

/-- Any concrete duplicate-helper invocation whose input is covered by the
module's AST measure fits within the fixed structural bound. -/
theorem duplicateComparisonUnits_le_structureBound {α κ : Type}
    [DecidableEq κ]
    (module : ParsedModuleV1)
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α)
    (covered : values.length ≤ astNodeMeasure module) :
    duplicateComparisonUnits key makeDiagnostic values ≤
      structureBound (astNodeMeasure module) := by
  have squareBound := duplicateComparisonUnits_le_square
    key makeDiagnostic values
  have measuredSquare :
      values.length * values.length ≤
        astNodeMeasure module * astNodeMeasure module :=
    Nat.mul_le_mul covered covered
  calc
    duplicateComparisonUnits key makeDiagnostic values ≤
        values.length * values.length := squareBound
    _ ≤ astNodeMeasure module * astNodeMeasure module := measuredSquare
    _ ≤ structureBound (astNodeMeasure module) := by
      simp only [structureBound]
      have firstFactor :
          astNodeMeasure module ≤ 32 * (astNodeMeasure module + 1) := by
        calc
          astNodeMeasure module ≤ astNodeMeasure module + 1 :=
            Nat.le_succ _
          _ = 1 * (astNodeMeasure module + 1) := by simp
          _ ≤ 32 * (astNodeMeasure module + 1) :=
            Nat.mul_le_mul_right _ (by omega)
      exact Nat.mul_le_mul firstFactor (Nat.le_succ _)

/-- Closed labels for every invocation of `duplicateDiagnostics` in the
structural validator. -/
inductive StructureDuplicateComparisonKind where
  | importSourceName
  | importLocalName
  | hiddenName
  | exportName
  | exportModuleReference
  | exportConstructor
  | pragmaTarget
deriving DecidableEq, Repr

/-- One duplicate-key comparison with its validator site and local offsets. -/
structure StructureDuplicateComparisonUnit where
  kind : StructureDuplicateComparisonKind
  siteSpan : SourceSpan
  candidateOrdinal : Nat
  seenOffset : Nat
deriving DecidableEq, Repr

private def tagDuplicateComparisons
    (kind : StructureDuplicateComparisonKind) (siteSpan : SourceSpan)
    (comparisons : List DuplicateComparisonUnit) :
    List StructureDuplicateComparisonUnit :=
  comparisons.map fun comparison =>
    { kind
      siteSpan
      candidateOrdinal := comparison.candidateOrdinal
      seenOffset := comparison.seenOffset }

private def duplicateRunTrace {α κ : Type} [DecidableEq κ]
    (kind : StructureDuplicateComparisonKind) (siteSpan : SourceSpan)
    (key : α → κ) (makeDiagnostic : α → StructuralDiagnostic)
    (values : List α) : List StructureDuplicateComparisonUnit :=
  tagDuplicateComparisons kind siteSpan
    (duplicateDiagnosticsRun key makeDiagnostic values).comparisons

/-- Duplicate-key comparisons performed within one import selection. -/
def importSelectionDuplicateComparisonTrace
    (selection : ImportSelection) : List StructureDuplicateComparisonUnit :=
  let named := namedImportEntries selection.payload.entries
  duplicateRunTrace .importSourceName selection.span
      (fun entry => entry.1.payload)
      (fun entry => .duplicateImportSourceName entry.1.span entry.1.payload)
      named ++
    duplicateRunTrace .importLocalName selection.span
      (fun entry => entry.2.payload)
      (fun entry => .duplicateImportLocalName entry.2.span entry.2.payload)
      named

/-- Duplicate-key comparisons performed within one import hiding clause. -/
def hidingDuplicateComparisonTrace
    (clause : HidingClause) : List StructureDuplicateComparisonUnit :=
  duplicateRunTrace .hiddenName clause.span
    (fun name => name.payload)
    (fun name => .duplicateHiddenName name.span name.payload)
    clause.payload.names

/-- Duplicate-key comparisons performed within a constructor selection. -/
def constructorSelectionDuplicateComparisonTrace
    (selection : Option ConstructorSelection) :
    List StructureDuplicateComparisonUnit :=
  match selection with
  | none => []
  | some located =>
      match located.payload with
      | .all _ => []
      | .named constructors =>
          duplicateRunTrace .exportConstructor located.span
            (fun name => name.payload)
            (fun name =>
              .duplicateExportConstructor name.span name.payload)
            (nonemptyToList constructors)

/-- Duplicate-key comparisons nested in one export item. -/
def exportItemDuplicateComparisonTrace
    (item : ExportItem) : List StructureDuplicateComparisonUnit :=
  constructorSelectionDuplicateComparisonTrace item.payload.constructors

/-- Project the local export items inspected by `localExportDiagnostics`. -/
def localExportItemsForDuplicateComparisons
    (entries : List ExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ | .allFrom _ _ => none

/-- Project the module references inspected by `localExportDiagnostics`. -/
def localExportReferencesForDuplicateComparisons
    (entries : List ExportEntry) : List ModuleReference :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .allFrom reference _ => some reference
    | .wildcard _ | .item _ => none

/-- Duplicate-key comparisons performed within a local export list. -/
def localExportDuplicateComparisonTrace
    (selection : LocalExportList) : List StructureDuplicateComparisonUnit :=
  let items :=
    localExportItemsForDuplicateComparisons selection.payload.entries
  let references :=
    localExportReferencesForDuplicateComparisons selection.payload.entries
  duplicateRunTrace .exportName selection.span
      (fun item => item.payload.name.payload)
      (fun item => .duplicateExportName
        item.payload.name.span item.payload.name.payload)
      items ++
    duplicateRunTrace .exportModuleReference selection.span
      ModuleReference.eraseLocations
      (fun reference => .duplicateExportModuleReference
        reference.span reference.eraseLocations)
      references ++
    items.flatMap exportItemDuplicateComparisonTrace

/-- Project the remote export items inspected by
`remoteExportDiagnostics`. -/
def remoteExportItemsForDuplicateComparisons
    (entries : List RemoteExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ => none

/-- Duplicate-key comparisons performed within a remote export selection. -/
def remoteExportDuplicateComparisonTrace
    (selection : RemoteExportSelection) :
    List StructureDuplicateComparisonUnit :=
  match selection.payload with
  | .dotWildcard _ => []
  | .braced entries =>
      let items := remoteExportItemsForDuplicateComparisons entries
      duplicateRunTrace .exportName selection.span
          (fun item => item.payload.name.payload)
          (fun item => .duplicateExportName
            item.payload.name.span item.payload.name.payload)
          items ++
        items.flatMap exportItemDuplicateComparisonTrace

/-- Duplicate-key comparisons performed within a pragma declaration. -/
def pragmaDuplicateComparisonTrace
    (declaration : PragmaDecl) : List StructureDuplicateComparisonUnit :=
  duplicateRunTrace .pragmaTarget declaration.span
    (fun target => target.payload)
    (fun target => .duplicatePragmaTarget target.span target.payload)
    declaration.payload.targets

/-- Duplicate-key comparisons performed from one top-level item.  The cases
mirror the only calls to `duplicateDiagnostics` in `Structure.lean`. -/
def topItemDuplicateComparisonTrace
    (item : TopItem) : List StructureDuplicateComparisonUnit :=
  match item.payload with
  | .importDecl declaration =>
      match declaration.payload.mode with
      | .module _ => []
      | .items selection hidingClause =>
          importSelectionDuplicateComparisonTrace selection ++
            match hidingClause with
            | none => []
            | some clause => hidingDuplicateComparisonTrace clause
  | .exportDecl declaration =>
      match declaration.payload with
      | .module _ _ => []
      | .local selection => localExportDuplicateComparisonTrace selection
      | .from _ selection => remoteExportDuplicateComparisonTrace selection
  | .pragmaDecl declaration => pragmaDuplicateComparisonTrace declaration
  | .dataDecl _ | .typeAliasDecl _ | .classDecl _ | .instanceDecl _ |
      .contractDecl _ | .functionDecl _ => []

/-- Executable duplicate-comparison trace for the complete parsed module. -/
def structureDuplicateComparisonTrace
    (module : ParsedModuleV1) : List StructureDuplicateComparisonUnit :=
  module.payload.items.flatMap topItemDuplicateComparisonTrace

/-- Number of duplicate-key list comparisons made for the module. -/
def structureDuplicateComparisonUnits (module : ParsedModuleV1) : Nat :=
  (structureDuplicateComparisonTrace module).length


end Structure

end Solcore.Surface.Multi

