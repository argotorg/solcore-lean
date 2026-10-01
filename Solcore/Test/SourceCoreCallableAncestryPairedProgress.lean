import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress

/-! The queue proof consumes actual factory equations. Final closure validation
and recipe success are conclusions, not assumptions supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableAncestryPairedProgress
open Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {initial final : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial)
    (completed : SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final) :
    SourceCoreCallableAncestryPairedPreparation.valid inputs final = true :=
  CallableAncestryPairedProgress.seeded_saturation_valid inputs seeded completed

example {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      SourceCoreCallableAncestryPairedPreparation.valid inputs final = true ∧
      ∃ recipes, final.views.attach.mapM (fun edge =>
        SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs final edge.val edge.property) = .ok recipes :=
  CallableAncestryPairedProgress.seeded_completion_total inputs seeded

/-- Successful compilation of the table preserves the independently defined
paired metadata authentication domain, including separately indexed parents. -/
example {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ table : Table, ∀ frame state, table.lookup? frame = some (some state) ↔ Authenticates inputs frame (some state) := by
  obtain ⟨table, _, validated, _⟩ := CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  refine ⟨table, ?_⟩
  intro frame state
  exact lookup_iff (CallableAncestryPairedValidation.valid_sound inputs validated)
    (CallableAncestryPairedValidation.valid_closed inputs validated)

end Solcore.Test.SourceCoreCallableAncestryPairedProgress
