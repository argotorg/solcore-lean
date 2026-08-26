import Solcore.Surface.Multi.Structure
import Solcore.Surface.Multi.StructureNodeVisitUnits

set_option autoImplicit false

namespace Solcore.Surface.Multi

/-!
This module materializes the diagnostic-insertion family of the structural
resource contract.  One event is recorded for every value placed in
`Structure.diagnosticCandidates`, before canonical deduplication and sorting.
The separate comparison family accounts for those later list operations.
-/

/-- One diagnostic insertion, distinguished by its position in the candidate
stream so repeated diagnostics remain separate charged events. -/
structure StructureDiagnosticInsertionUnit where
  ordinal : Nat
  diagnostic : StructuralDiagnostic
deriving DecidableEq, Repr

/-- The exact collector-order stream of diagnostic insertions performed by the
structural collectors. -/
def structureDiagnosticInsertionTrace
    (module : ParsedModuleV1) : List StructureDiagnosticInsertionUnit :=
  (Structure.diagnosticCandidates module).mapIdx fun ordinal diagnostic =>
    { ordinal, diagnostic }

/-- Executable number of diagnostic-insertion units. -/
def structureDiagnosticInsertionUnits (module : ParsedModuleV1) : Nat :=
  (structureDiagnosticInsertionTrace module).length

@[simp] theorem structureDiagnosticInsertionTrace_length
    (module : ParsedModuleV1) :
    (structureDiagnosticInsertionTrace module).length =
      (Structure.diagnosticCandidates module).length := by
  simp [structureDiagnosticInsertionTrace]

/-- Looking up an insertion event recovers the candidate at the same ordinal. -/
theorem structureDiagnosticInsertionTrace_get?
    (module : ParsedModuleV1) (ordinal : Nat) :
    (structureDiagnosticInsertionTrace module)[ordinal]? =
      (Structure.diagnosticCandidates module)[ordinal]?.map fun diagnostic =>
        { ordinal, diagnostic } := by
  simp [structureDiagnosticInsertionTrace]

private theorem diagnosticInsertionTraceFrom_nodup
    (start : Nat) (diagnostics : List StructuralDiagnostic) :
    (diagnostics.mapIdx fun ordinal diagnostic =>
      ({ ordinal := start + ordinal, diagnostic } :
        StructureDiagnosticInsertionUnit)).Nodup := by
  induction diagnostics generalizing start with
  | nil => simp
  | cons head tail induction =>
      rw [List.mapIdx_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_mapIdx] at member
        rcases member with ⟨ordinal, _within, same⟩
        have ordinalSame :=
          congrArg StructureDiagnosticInsertionUnit.ordinal same
        simp only at ordinalSame
        omega
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          induction (start := start + 1)

/-- Candidate insertions remain distinct even when their diagnostics compare
equal and are later deduplicated. -/
theorem structureDiagnosticInsertionTrace_nodup
    (module : ParsedModuleV1) :
    (structureDiagnosticInsertionTrace module).Nodup := by
  simpa [structureDiagnosticInsertionTrace] using
    diagnosticInsertionTraceFrom_nodup 0
      (Structure.diagnosticCandidates module)

/-- Insertion accounting is exactly the length of the actual candidate stream. -/
@[simp] theorem structureDiagnosticInsertionUnits_eq_candidates_length
    (module : ParsedModuleV1) :
    structureDiagnosticInsertionUnits module =
      (Structure.diagnosticCandidates module).length := by
  simp [structureDiagnosticInsertionUnits]

private theorem nodup_length_le_of_subset
    {alpha : Type}
    {left right : List alpha} (unique : left.Nodup)
    (subset : left ⊆ right) : left.length ≤ right.length := by
  induction left generalizing right with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at unique
      have headMember : head ∈ right := subset (by simp)
      rcases List.append_of_mem headMember with ⟨before, after, rightEq⟩
      subst right
      have tailSubset : tail ⊆ before ++ after := by
        intro value valueMember
        have inFull : value ∈ before ++ head :: after :=
          subset (by simp [valueMember])
        simp only [List.mem_append, List.mem_cons] at inFull ⊢
        rcases inFull with inBefore | equalOrAfter
        · exact Or.inl inBefore
        · rcases equalOrAfter with equal | inAfter
          · exact False.elim (unique.1 (equal ▸ valueMember))
          · exact Or.inr inAfter
      have shorter := induction unique.2 tailSubset
      simp only [List.length_append] at shorter
      simp only [List.length_cons, List.length_append]
      omega

/-- Canonicalization never creates an uncharged diagnostic: the final report
has at most as many entries as the candidate-insertion stream. -/
theorem structureDiagnostics_length_le_insertionUnits
    (module : ParsedModuleV1) :
    (Structure.diagnostics module).length ≤
      structureDiagnosticInsertionUnits module := by
  rw [structureDiagnosticInsertionUnits_eq_candidates_length]
  apply nodup_length_le_of_subset (Structure.diagnostics_nodup module)
  intro diagnostic member
  exact Structure.mem_diagnostics.mp member

end Solcore.Surface.Multi
