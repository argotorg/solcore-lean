import Solcore.Frontend.SourceInference.NodeGraphRecorderAutomation

set_option autoImplicit false

namespace Tests.SourceNodeGraphAutomation

open Solcore.Frontend.SourceInference

private def StateTail := Nat × State
private def NestedStateTail := Bool × StateTail

example (pair : NestedStateTail) : ∃ _ : State, True := by
  occurrence_split_state_pairs
  rename_i flag count state
  exact ⟨state, trivial⟩

example (pair : State × Nat) : pair.2 = pair.2 := by
  occurrence_split_state_pairs
  guard_hyp pair : State × Nat
  rfl

private def LeftEquations (a b c : Nat) := a = b ∧ (True ∧ b = c)
private def RightEquations (c d : Nat) := (True ∨ False) ∧ c = d

example (a b c d : Nat)
    (equations : LeftEquations a b c ∧ RightEquations c d) :
    a = b ∧ b = c ∧ c = d := by
  occurrence_split_conjunctions
  exact ⟨by assumption, by assumption, by assumption⟩

example (_ignored : True ∧ (True ∨ False)) : True := by
  occurrence_split_conjunctions
  trivial

end Tests.SourceNodeGraphAutomation
