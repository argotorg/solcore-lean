import Solcore.Surface.Multi.StructureLeastSpanComparisonUnits
import Solcore.Surface.Multi.StructureDuplicateComparisonUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
This module combines the executable structural-resource counters without
changing what any component counts.  The ledger keeps each recorded family
visible, while `structureActualUnits` is their exact sum.
-/

/-- The six independently recorded structural-resource families for one
parsed module. -/
structure StructureResourceLedger where
  nodeVisits : Nat
  diagnosticInsertions : Nat
  duplicateComparisons : Nat
  canonicalDedupComparisons : Nat
  canonicalOrderingComparisons : Nat
  leastSpanComparisons : Nat
deriving DecidableEq, Repr

namespace StructureResourceLedger

/-- Total charged units represented by a structural-resource ledger. -/
def total (ledger : StructureResourceLedger) : Nat :=
  ledger.nodeVisits +
    ledger.diagnosticInsertions +
    ledger.duplicateComparisons +
    ledger.canonicalDedupComparisons +
    ledger.canonicalOrderingComparisons +
    ledger.leastSpanComparisons

@[simp] theorem total_equation (ledger : StructureResourceLedger) :
    ledger.total =
      ledger.nodeVisits +
        ledger.diagnosticInsertions +
        ledger.duplicateComparisons +
        ledger.canonicalDedupComparisons +
        ledger.canonicalOrderingComparisons +
        ledger.leastSpanComparisons := by
  rfl

theorem nodeVisits_le_total (ledger : StructureResourceLedger) :
    ledger.nodeVisits ≤ ledger.total := by
  simp only [total]
  omega

theorem diagnosticInsertions_le_total (ledger : StructureResourceLedger) :
    ledger.diagnosticInsertions ≤ ledger.total := by
  simp only [total]
  omega

theorem duplicateComparisons_le_total (ledger : StructureResourceLedger) :
    ledger.duplicateComparisons ≤ ledger.total := by
  simp only [total]
  omega

theorem canonicalDedupComparisons_le_total
    (ledger : StructureResourceLedger) :
    ledger.canonicalDedupComparisons ≤ ledger.total := by
  simp only [total]
  omega

theorem canonicalOrderingComparisons_le_total
    (ledger : StructureResourceLedger) :
    ledger.canonicalOrderingComparisons ≤ ledger.total := by
  simp only [total]
  omega

theorem leastSpanComparisons_le_total (ledger : StructureResourceLedger) :
    ledger.leastSpanComparisons ≤ ledger.total := by
  simp only [total]
  omega

end StructureResourceLedger

/-- Build the structural-resource ledger from the six executable counters. -/
def structureResourceLedger
    (module : ParsedModuleV1) : StructureResourceLedger :=
  {
    nodeVisits := structureNodeVisitUnits module
    diagnosticInsertions := structureDiagnosticInsertionUnits module
    duplicateComparisons := Structure.structureDuplicateComparisonUnits module
    canonicalDedupComparisons :=
      Structure.structureCanonicalDedupComparisonUnits module
    canonicalOrderingComparisons :=
      Structure.structureCanonicalOrderingComparisonUnits module
    leastSpanComparisons := Structure.structureLeastSpanComparisonUnits module
  }

@[simp] theorem structureResourceLedger_nodeVisits
    (module : ParsedModuleV1) :
    (structureResourceLedger module).nodeVisits =
      structureNodeVisitUnits module := by
  rfl

@[simp] theorem structureResourceLedger_diagnosticInsertions
    (module : ParsedModuleV1) :
    (structureResourceLedger module).diagnosticInsertions =
      structureDiagnosticInsertionUnits module := by
  rfl

@[simp] theorem structureResourceLedger_duplicateComparisons
    (module : ParsedModuleV1) :
    (structureResourceLedger module).duplicateComparisons =
      Structure.structureDuplicateComparisonUnits module := by
  rfl

@[simp] theorem structureResourceLedger_canonicalDedupComparisons
    (module : ParsedModuleV1) :
    (structureResourceLedger module).canonicalDedupComparisons =
      Structure.structureCanonicalDedupComparisonUnits module := by
  rfl

@[simp] theorem structureResourceLedger_canonicalOrderingComparisons
    (module : ParsedModuleV1) :
    (structureResourceLedger module).canonicalOrderingComparisons =
      Structure.structureCanonicalOrderingComparisonUnits module := by
  rfl

@[simp] theorem structureResourceLedger_leastSpanComparisons
    (module : ParsedModuleV1) :
    (structureResourceLedger module).leastSpanComparisons =
      Structure.structureLeastSpanComparisonUnits module := by
  rfl

/-- Executable total for all structural-resource families recorded by the
current validator accounting. -/
def structureActualUnits (module : ParsedModuleV1) : Nat :=
  (structureResourceLedger module).total

/-- The combined counter is definitionally the sum of all six recorded
families. -/
@[simp] theorem structureActualUnits_equation (module : ParsedModuleV1) :
    structureActualUnits module =
      structureNodeVisitUnits module +
        structureDiagnosticInsertionUnits module +
        Structure.structureDuplicateComparisonUnits module +
        Structure.structureCanonicalDedupComparisonUnits module +
        Structure.structureCanonicalOrderingComparisonUnits module +
        Structure.structureLeastSpanComparisonUnits module := by
  rfl

/-- Every parsed module incurs at least its root node visit. -/
theorem structureActualUnits_positive (module : ParsedModuleV1) :
    0 < structureActualUnits module := by
  have nodePositive := structureNodeVisitUnits_positive module
  simp only [structureActualUnits_equation]
  omega

theorem structureNodeVisitUnits_le_actual (module : ParsedModuleV1) :
    structureNodeVisitUnits module ≤ structureActualUnits module := by
  exact StructureResourceLedger.nodeVisits_le_total
    (structureResourceLedger module)

theorem structureDiagnosticInsertionUnits_le_actual
    (module : ParsedModuleV1) :
    structureDiagnosticInsertionUnits module ≤ structureActualUnits module := by
  exact StructureResourceLedger.diagnosticInsertions_le_total
    (structureResourceLedger module)

theorem structureDuplicateComparisonUnits_le_actual
    (module : ParsedModuleV1) :
    Structure.structureDuplicateComparisonUnits module ≤
      structureActualUnits module := by
  exact StructureResourceLedger.duplicateComparisons_le_total
    (structureResourceLedger module)

theorem structureCanonicalDedupComparisonUnits_le_actual
    (module : ParsedModuleV1) :
    Structure.structureCanonicalDedupComparisonUnits module ≤
      structureActualUnits module := by
  exact StructureResourceLedger.canonicalDedupComparisons_le_total
    (structureResourceLedger module)

theorem structureCanonicalOrderingComparisonUnits_le_actual
    (module : ParsedModuleV1) :
    Structure.structureCanonicalOrderingComparisonUnits module ≤
      structureActualUnits module := by
  exact StructureResourceLedger.canonicalOrderingComparisons_le_total
    (structureResourceLedger module)

theorem structureLeastSpanComparisonUnits_le_actual
    (module : ParsedModuleV1) :
    Structure.structureLeastSpanComparisonUnits module ≤
      structureActualUnits module := by
  exact StructureResourceLedger.leastSpanComparisons_le_total
    (structureResourceLedger module)

/-- Upper envelope obtained from the bounds already proved for both canonical
list passes.  The other four families remain visible at their exact counts. -/
def structureKnownUpperEnvelope (module : ParsedModuleV1) : Nat :=
  let insertions := structureDiagnosticInsertionUnits module
  structureNodeVisitUnits module +
    insertions +
    Structure.structureDuplicateComparisonUnits module +
    insertions * insertions +
    insertions * insertions +
    Structure.structureLeastSpanComparisonUnits module

@[simp] theorem structureKnownUpperEnvelope_equation
    (module : ParsedModuleV1) :
    structureKnownUpperEnvelope module =
      structureNodeVisitUnits module +
        structureDiagnosticInsertionUnits module +
        Structure.structureDuplicateComparisonUnits module +
        structureDiagnosticInsertionUnits module *
          structureDiagnosticInsertionUnits module +
        structureDiagnosticInsertionUnits module *
          structureDiagnosticInsertionUnits module +
        Structure.structureLeastSpanComparisonUnits module := by
  rfl

/-- Existing per-pass comparison theorems reduce the total-accounting bound
to the remaining module-level envelope inequality. -/
theorem structureActualUnits_le_knownUpperEnvelope
    (module : ParsedModuleV1) :
    structureActualUnits module ≤ structureKnownUpperEnvelope module := by
  have dedupBound :
      Structure.structureCanonicalDedupComparisonUnits module ≤
        structureDiagnosticInsertionUnits module *
          structureDiagnosticInsertionUnits module := by
    simpa only [structureDiagnosticInsertionUnits_eq_candidates_length] using
      Structure.structureCanonicalDedupComparisonUnits_le_candidates_square
        module
  have orderingBound :=
    Structure.structureCanonicalOrderingComparisonUnits_le_insertion_square
      module
  simp only [structureActualUnits_equation,
    structureKnownUpperEnvelope_equation]
  omega

/-- Any proof of the remaining envelope inequality closes the advertised
structural bound for the exact combined counter. -/
theorem structureActualUnits_le_structureBound_of_envelope
    (module : ParsedModuleV1)
    (envelopeBound :
      structureKnownUpperEnvelope module ≤
        structureBound (astNodeMeasure module)) :
    structureActualUnits module ≤ structureBound (astNodeMeasure module) := by
  exact Nat.le_trans
    (structureActualUnits_le_knownUpperEnvelope module)
    envelopeBound

end Solcore.Surface.Multi
