import Solcore.Frontend.SourceCoreDirectLinking

/-! Small checked laws for the specialized direct-call linking boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDirectLinking

@[simp] theorem LinkedProgram.findEntry?_empty (key : SpecializationKey) :
    ({ entries := [] : LinkedProgram }).findEntry? key = none := by
  rfl

theorem LinkedEntry.run?_of_matching_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (typesEqual : inputs.map Core.Value.type = entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = some (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store)) := by
  simp [LinkedEntry.run?, typesEqual]

theorem LinkedEntry.run?_of_mismatched_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠
      entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = none := by
  simp [LinkedEntry.run?, mismatch]

@[simp] theorem link_budgetExhausted (program : CheckedProgram) (plan : Plan)
    (next : SpecializationKey)
    (pending : List SourceSpecializationWorklist.Request) :
    link program (.budgetExhausted plan next pending) =
      .error (.budgetExhausted next pending.length) := by
  rfl

end Solcore.Frontend.SourceCoreDirectLinking
