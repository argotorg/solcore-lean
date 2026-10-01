import Solcore.SourceSemantics.CoreLowering.CallableAncestryWorklist

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Kernel-checked actual seed/traversal contracts. These cover the current
independent metadata transition graph; they do not assert that arbitrary native
call frames were emitted by that graph or that every artifact seeds/validates. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryWorklist
open Solcore Solcore.Frontend SourceInference
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryMetadata CallableAncestryCache CallableAncestryCardinality CallableAncestryWorklist

example {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {initial : SourceCoreCallableAncestryCache.Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    StatesValid owned initial.states ∧ CoversRoots owned initial.states :=
  seed_spec owned inputs seeded

example {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {initial : SourceCoreCallableAncestryCache.Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPreparation.saturate inputs
      (SourceCoreCallableAncestryPreparation.capacity inputs initial) 0 initial = .ok final ∧
      StatesValid owned final.states := seeded_saturation_total owned inputs seeded

example {checked : Checked} {base : Base checked}
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base) (initial : SourceCoreCallableAncestryCache.Table) :
    (keySpace inputs initial.states).length = SourceCoreCallableAncestryPreparation.capacity inputs initial :=
  universe_length inputs initial

example (alphabet : List RequirementId) (lengths : List Nat) :
    (FiniteProfiles.profiles alphabet lengths).length = alphabet.length ^ lengths.sum := profiles_length alphabet lengths

example : (FiniteProfiles.profiles [] [0, 0, 0]).length = 1 := by decide
example : (FiniteProfiles.profiles [⟨2⟩, ⟨4⟩] [1, 0, 2]).length = 8 := by decide

end Tests.SourceCoreCallableAncestryWorklist
