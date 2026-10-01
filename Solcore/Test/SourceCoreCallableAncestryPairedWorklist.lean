import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual worklist totality after successful named seeding. These consumers
do not assume a successful final saturation result, invent a traversal fuel,
or treat final validation/native-frame coverage as already established. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedWorklist
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedWorklist
abbrev State := SourceCoreCallableAncestryReadRecipes.State

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table)
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      StatesValid inputs final.states := seeded_saturation_total inputs seeded

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table)
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial ≠
        .error .cardinalityExhausted := by
  obtain ⟨final, completed, _⟩ := seeded_saturation_total inputs seeded
  rw [completed]
  intro impossible
  cases impossible

example {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    CallableAncestryPairedProfiles.RootsCoherent (namedRoots inputs) :=
  CallableAncestryPairedProfiles.seeded_coherent (named_roots_seeded inputs)

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {states : List State}
    (valid : StatesValid inputs states) {state : State} {frame : Frame}
    (authentic : Authenticates inputs frame (some state)) :
    ∃ position output, SourceCoreCallableAncestryPairedPreparation.intern states state = .ok (position, output) ∧
      StatesValid inputs output ∧ states ⊆ output ∧ state ∈ output := intern_total valid ⟨frame, authentic⟩

end Tests.SourceCoreCallableAncestryPairedWorklist
