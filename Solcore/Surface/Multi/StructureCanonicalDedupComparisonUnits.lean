import Solcore.Surface.Multi.StructureDiagnosticInsertionUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

/-!
The canonical structural report removes repeated diagnostic values before it
sorts them.  This module instruments exactly that equality-comparison pass.
Ordering comparisons remain a separate accounting slice.
-/

/-- Result and visited offsets from one `diagnosticOccurs` lookup. -/
structure DiagnosticOccursRun where
  occurs : Bool
  comparedOffsets : List Nat
deriving DecidableEq, Repr

/-- Counted counterpart of `diagnosticOccurs`, stopping at the first equal
diagnostic exactly as the validator does. -/
def diagnosticOccursRun
    (diagnostic : StructuralDiagnostic) :
    List StructuralDiagnostic → DiagnosticOccursRun
  | [] => { occurs := false, comparedOffsets := [] }
  | value :: rest =>
      if diagnostic = value then
        { occurs := true, comparedOffsets := [0] }
      else
        let later := diagnosticOccursRun diagnostic rest
        { occurs := later.occurs
          comparedOffsets := 0 :: later.comparedOffsets.map Nat.succ }

@[simp] theorem diagnosticOccursRun_occurs
    (diagnostic : StructuralDiagnostic)
    (values : List StructuralDiagnostic) :
    (diagnosticOccursRun diagnostic values).occurs =
      diagnosticOccurs diagnostic values := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp only [diagnosticOccursRun, diagnosticOccurs]
      split
      · rfl
      · exact induction

theorem diagnosticOccursRun_comparisons_le
    (diagnostic : StructuralDiagnostic)
    (values : List StructuralDiagnostic) :
    (diagnosticOccursRun diagnostic values).comparedOffsets.length ≤
      values.length := by
  induction values with
  | nil => simp [diagnosticOccursRun]
  | cons value rest induction =>
      simp only [diagnosticOccursRun]
      split
      · simp
      · simp only [List.length_cons, List.length_map]
        omega

/-- One equality comparison in canonical diagnostic deduplication. -/
structure CanonicalDedupComparisonUnit where
  candidateOrdinal : Nat
  laterOffset : Nat
deriving DecidableEq, Repr

/-- Deduplicated diagnostics and the comparisons that selected them. -/
structure DeduplicateDiagnosticsRun where
  diagnostics : List StructuralDiagnostic
  comparisons : List CanonicalDedupComparisonUnit
deriving DecidableEq, Repr

/-- Counted counterpart of `deduplicateDiagnostics`, with ordinals measured in
the original candidate list. -/
def deduplicateDiagnosticsRunFrom
    (candidateOrdinal : Nat) :
    List StructuralDiagnostic → DeduplicateDiagnosticsRun
  | [] => { diagnostics := [], comparisons := [] }
  | diagnostic :: rest =>
      let occurrence := diagnosticOccursRun diagnostic rest
      let current := occurrence.comparedOffsets.map fun laterOffset =>
        { candidateOrdinal, laterOffset }
      let later := deduplicateDiagnosticsRunFrom
        (candidateOrdinal + 1) rest
      { diagnostics :=
          if occurrence.occurs then later.diagnostics
          else diagnostic :: later.diagnostics
        comparisons := current ++ later.comparisons }

/-- Count canonical deduplication from the first candidate. -/
def deduplicateDiagnosticsRun
    (values : List StructuralDiagnostic) : DeduplicateDiagnosticsRun :=
  deduplicateDiagnosticsRunFrom 0 values

@[simp] theorem deduplicateDiagnosticsRunFrom_diagnostics
    (candidateOrdinal : Nat) (values : List StructuralDiagnostic) :
    (deduplicateDiagnosticsRunFrom candidateOrdinal values).diagnostics =
      deduplicateDiagnostics values := by
  induction values generalizing candidateOrdinal with
  | nil => rfl
  | cons diagnostic rest induction =>
      simp only [deduplicateDiagnosticsRunFrom, deduplicateDiagnostics]
      rw [diagnosticOccursRun_occurs, induction]

/-- Erasing the comparison trace recovers the validator's exact deduplicated
diagnostic list. -/
@[simp] theorem deduplicateDiagnosticsRun_diagnostics
    (values : List StructuralDiagnostic) :
    (deduplicateDiagnosticsRun values).diagnostics =
      deduplicateDiagnostics values := by
  exact deduplicateDiagnosticsRunFrom_diagnostics 0 values

theorem deduplicateDiagnosticsRunFrom_comparisons_le
    (candidateOrdinal : Nat) (values : List StructuralDiagnostic) :
    (deduplicateDiagnosticsRunFrom candidateOrdinal values).comparisons.length ≤
      values.length * values.length := by
  induction values generalizing candidateOrdinal with
  | nil => simp [deduplicateDiagnosticsRunFrom]
  | cons diagnostic rest induction =>
      simp only [deduplicateDiagnosticsRunFrom, List.length_append,
        List.length_map]
      have currentBound :=
        diagnosticOccursRun_comparisons_le diagnostic rest
      have laterBound := induction (candidateOrdinal := candidateOrdinal + 1)
      simp only [List.length_cons] at laterBound ⊢
      apply Nat.le_trans (Nat.add_le_add currentBound laterBound)
      calc
        rest.length + rest.length * rest.length =
            rest.length * (rest.length + 1) := by
              rw [Nat.mul_add]
              simp [Nat.add_comm]
        _ ≤ (rest.length + 1) * (rest.length + 1) :=
          Nat.mul_le_mul (Nat.le_succ _) (Nat.le_refl _)

/-- Canonical deduplication performs at most the square of the candidate count
many equality comparisons. -/
theorem deduplicateDiagnosticsRun_comparisons_le_square
    (values : List StructuralDiagnostic) :
    (deduplicateDiagnosticsRun values).comparisons.length ≤
      values.length * values.length := by
  exact deduplicateDiagnosticsRunFrom_comparisons_le 0 values

/-- Exact canonical-deduplication comparison trace for a parsed module. -/
def structureCanonicalDedupComparisonTrace
    (module : ParsedModuleV1) : List CanonicalDedupComparisonUnit :=
  (deduplicateDiagnosticsRun
    (diagnosticCandidates module)).comparisons

/-- Executable number of comparisons in canonical deduplication. -/
def structureCanonicalDedupComparisonUnits
    (module : ParsedModuleV1) : Nat :=
  (structureCanonicalDedupComparisonTrace module).length

/-- The counted deduplication result, after the unchanged ordering pass, is
exactly the validator's canonical diagnostic list. -/
theorem deduplicateDiagnosticsRun_mergeSort_eq_diagnostics
    (module : ParsedModuleV1) :
    (deduplicateDiagnosticsRun
        (diagnosticCandidates module)).diagnostics.mergeSort
          StructuralDiagnostic.le =
      diagnostics module := by
  rw [deduplicateDiagnosticsRun_diagnostics]
  rfl

/-- Module-level canonical deduplication respects the candidate-count square
bound. -/
theorem structureCanonicalDedupComparisonUnits_le_candidates_square
    (module : ParsedModuleV1) :
    structureCanonicalDedupComparisonUnits module ≤
      (diagnosticCandidates module).length *
        (diagnosticCandidates module).length := by
  exact deduplicateDiagnosticsRun_comparisons_le_square
    (diagnosticCandidates module)

end Structure

end Solcore.Surface.Multi
