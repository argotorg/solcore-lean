import Solcore.Surface.Multi.StructureCanonicalDedupComparisonUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

namespace Structure

/-!
This module instruments the comparison calls in the `List.mergeSort` used to
put structural diagnostics into canonical order.  It follows the same
contiguous split, recursive order, and stable merge branches as Lean's logical
`mergeSort` definition.
-/

/-- One ordering comparison made while merging two sorted lists. -/
structure ListOrderingComparisonUnit (alpha : Type) where
  left : alpha
  right : alpha
deriving DecidableEq, Repr

/-- The comparison trace of Lean's logical stable-merge definition. -/
def mergeOrderingComparisonTrace {alpha : Type}
    (le : alpha → alpha → Bool) :
    List alpha → List alpha → List (ListOrderingComparisonUnit alpha)
  | [], _ => []
  | _, [] => []
  | left :: lefts, right :: rights =>
      { left, right } ::
        if le left right then
          mergeOrderingComparisonTrace le lefts (right :: rights)
        else
          mergeOrderingComparisonTrace le (left :: lefts) rights
termination_by lefts rights => lefts.length + rights.length

/-- One merge compares no more pairs than the combined input length. -/
theorem mergeOrderingComparisonTrace_length_le {alpha : Type}
    (le : alpha → alpha → Bool) (lefts rights : List alpha) :
    (mergeOrderingComparisonTrace le lefts rights).length ≤
      lefts.length + rights.length := by
  induction lefts, rights using mergeOrderingComparisonTrace.induct with
  | case1 => simp [mergeOrderingComparisonTrace]
  | case2 => simp [mergeOrderingComparisonTrace]
  | case3 left lefts right rights leftInduction rightInduction =>
      simp only [mergeOrderingComparisonTrace, List.length_cons]
        at leftInduction rightInduction ⊢
      split
      · omega
      · omega

open List.MergeSort.Internal in
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- Comparison trace of Lean's logical stable merge sort. -/
def mergeSortOrderingComparisonTrace {alpha : Type} :
    ∀ (values : List alpha) (le : alpha → alpha → Bool),
      List (ListOrderingComparisonUnit alpha)
  | [], _ => []
  | [_], _ => []
  | first :: second :: rest, le =>
      let halves := splitInTwo ⟨first :: second :: rest, rfl⟩
      have := by simpa using halves.2.2
      have := by simpa using halves.1.2
      mergeSortOrderingComparisonTrace halves.1.1 le ++
        mergeSortOrderingComparisonTrace halves.2.1 le ++
        mergeOrderingComparisonTrace le
          (halves.1.1.mergeSort le) (halves.2.1.mergeSort le)
termination_by values => values.length

/-- Stable merge sort makes at most the square of the input length many
ordering comparisons. -/
theorem mergeSortOrderingComparisonTrace_length_le_square {alpha : Type}
    (values : List alpha) (le : alpha → alpha → Bool) :
    (mergeSortOrderingComparisonTrace values le).length ≤
      values.length * values.length := by
  induction values, le using mergeSortOrderingComparisonTrace.induct with
  | case1 le => simp [mergeSortOrderingComparisonTrace]
  | case2 le head => simp [mergeSortOrderingComparisonTrace]
  | case3 first second rest le halves secondLength firstLength
      leftBound rightBound =>
      have mergeBound := mergeOrderingComparisonTrace_length_le le
        (halves.1.1.mergeSort le) (halves.2.1.mergeSort le)
      simp only [List.length_mergeSort] at mergeBound
      simp only [mergeSortOrderingComparisonTrace, List.length_append]
      have halfSum : halves.1.1.length + halves.2.1.length =
          (first :: second :: rest).length := by
        rw [halves.1.2, halves.2.2]
        simp only [List.length_cons]
        omega
      have leftPositive : 1 ≤ halves.1.1.length := by
        rw [halves.1.2]
        simp only [List.length_cons]
        omega
      have rightPositive : 1 ≤ halves.2.1.length := by
        rw [halves.2.2]
        simp only [List.length_cons]
        omega
      have leftToCross : halves.1.1.length ≤
          halves.1.1.length * halves.2.1.length := by
        calc
          halves.1.1.length = halves.1.1.length * 1 := by simp
          _ ≤ halves.1.1.length * halves.2.1.length :=
            Nat.mul_le_mul_left _ rightPositive
      have rightToCross : halves.2.1.length ≤
          halves.1.1.length * halves.2.1.length := by
        calc
          halves.2.1.length = 1 * halves.2.1.length := by simp
          _ ≤ halves.1.1.length * halves.2.1.length :=
            Nat.mul_le_mul_right _ leftPositive
      apply Nat.le_trans
        (Nat.add_le_add (Nat.add_le_add leftBound rightBound) mergeBound)
      calc
        halves.1.1.length * halves.1.1.length +
              halves.2.1.length * halves.2.1.length +
              (halves.1.1.length + halves.2.1.length) ≤
            (halves.1.1.length + halves.2.1.length) *
              (halves.1.1.length + halves.2.1.length) := by
                rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                rw [Nat.mul_comm halves.2.1.length halves.1.1.length]
                omega
        _ = (first :: second :: rest).length *
              (first :: second :: rest).length :=
          congrArg (fun value => value * value) halfSum

/-- Canonically ordered diagnostics together with their ordering comparisons. -/
structure CanonicalOrderingRun where
  diagnostics : List StructuralDiagnostic
  comparisons : List (ListOrderingComparisonUnit StructuralDiagnostic)
deriving DecidableEq, Repr

/-- Run the unchanged canonical ordering and materialize its logical
comparison trace. -/
def canonicalOrderingRun
    (values : List StructuralDiagnostic) : CanonicalOrderingRun := {
  diagnostics := values.mergeSort StructuralDiagnostic.le
  comparisons :=
    mergeSortOrderingComparisonTrace values StructuralDiagnostic.le
}

/-- Canonical ordering starts from the exact output of the counted
deduplication pass. -/
def structureCanonicalOrderingRun
    (module : ParsedModuleV1) : CanonicalOrderingRun :=
  canonicalOrderingRun
    (deduplicateDiagnosticsRun
      (diagnosticCandidates module)).diagnostics

/-- The counted ordering run returns exactly the validator's canonical list. -/
@[simp] theorem structureCanonicalOrderingRun_diagnostics
    (module : ParsedModuleV1) :
    (structureCanonicalOrderingRun module).diagnostics =
      diagnostics module := by
  exact deduplicateDiagnosticsRun_mergeSort_eq_diagnostics module

/-- Executable canonical-ordering comparison trace for one module. -/
def structureCanonicalOrderingComparisonTrace
    (module : ParsedModuleV1) :
    List (ListOrderingComparisonUnit StructuralDiagnostic) :=
  (structureCanonicalOrderingRun module).comparisons

/-- Number of ordering comparisons made for the canonical report. -/
def structureCanonicalOrderingComparisonUnits
    (module : ParsedModuleV1) : Nat :=
  (structureCanonicalOrderingComparisonTrace module).length

/-- Ordering comparisons are bounded by the square of the diagnostic
insertion count. -/
theorem structureCanonicalOrderingComparisonUnits_le_insertion_square
    (module : ParsedModuleV1) :
    structureCanonicalOrderingComparisonUnits module ≤
      structureDiagnosticInsertionUnits module *
        structureDiagnosticInsertionUnits module := by
  have sortBound := mergeSortOrderingComparisonTrace_length_le_square
    (deduplicateDiagnosticsRun
      (diagnosticCandidates module)).diagnostics
      StructuralDiagnostic.le
  have deduplicatedLength :
      (deduplicateDiagnosticsRun
        (diagnosticCandidates module)).diagnostics.length ≤
        structureDiagnosticInsertionUnits module := by
    have outputEq := congrArg List.length
      (deduplicateDiagnosticsRun_mergeSort_eq_diagnostics module)
    simp only [List.length_mergeSort] at outputEq
    calc
      _ = (diagnostics module).length := outputEq
      _ ≤ structureDiagnosticInsertionUnits module :=
        structureDiagnostics_length_le_insertionUnits module
  exact Nat.le_trans sortBound
    (Nat.mul_le_mul deduplicatedLength deduplicatedLength)

end Structure

end Solcore.Surface.Multi
