import Solcore.Surface.Multi.StructureResourceAccounting
import Solcore.Surface.Multi.StructureDiagnosticInsertionBound
import Solcore.Surface.Multi.StructureDuplicateComparisonBound
import Solcore.Surface.Multi.StructureLeastSpanComparisonBound

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
This module closes the numeric structural-resource contract.  The exact
six-family ledger remains executable; the proof below combines its component
bounds without changing what any counter records.
-/

/-- The fixed quadratic structural bound is sufficient for every unit charged
by the executable six-family resource ledger. -/
theorem structureBound_sufficient (module : ParsedModuleV1) :
    structureActualUnits module ≤
      structureBound (astNodeMeasure module) := by
  have insertionBound :=
    structureDiagnosticInsertionUnits_le_astNodeMeasure module
  have duplicateBound :=
    Structure.structureDuplicateComparisonUnits_le_three_astNodeMeasure_square
      module
  have dedupCandidateBound :=
    Structure.structureCanonicalDedupComparisonUnits_le_candidates_square
      module
  have dedupBound :
      Structure.structureCanonicalDedupComparisonUnits module ≤
        astNodeMeasure module * astNodeMeasure module := by
    rw [← structureDiagnosticInsertionUnits_eq_candidates_length]
      at dedupCandidateBound
    exact Nat.le_trans dedupCandidateBound
      (Nat.mul_le_mul insertionBound insertionBound)
  have orderingCandidateBound :=
    Structure.structureCanonicalOrderingComparisonUnits_le_insertion_square
      module
  have orderingBound :
      Structure.structureCanonicalOrderingComparisonUnits module ≤
        astNodeMeasure module * astNodeMeasure module := by
    exact Nat.le_trans orderingCandidateBound
      (Nat.mul_le_mul insertionBound insertionBound)
  have leastBound :=
    Structure.structureLeastSpanComparisonUnits_le_astNodeMeasure module
  rw [structureActualUnits_equation,
    structureNodeVisitUnits_eq_astNodeMeasure]
  have coarse :
      astNodeMeasure module + structureDiagnosticInsertionUnits module +
          Structure.structureDuplicateComparisonUnits module +
          Structure.structureCanonicalDedupComparisonUnits module +
          Structure.structureCanonicalOrderingComparisonUnits module +
          Structure.structureLeastSpanComparisonUnits module ≤
        5 * (astNodeMeasure module * astNodeMeasure module) +
          3 * astNodeMeasure module := by
    omega
  apply Nat.le_trans coarse
  simp only [structureBound, Nat.mul_add, Nat.add_mul, Nat.mul_one]
  rw [show 32 * astNodeMeasure module * astNodeMeasure module =
      32 * (astNodeMeasure module * astNodeMeasure module) by ac_rfl]
  omega

end Solcore.Surface.Multi
