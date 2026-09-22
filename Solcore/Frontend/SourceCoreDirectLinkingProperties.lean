import Solcore.Frontend.SourceCoreDirectLinking

/-! Small checked laws for the specialized direct-call linking boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDirectLinking

@[simp] theorem LinkedProgram.findEntry?_empty (key : SpecializationKey) :
    ({ entries := [] : LinkedProgram }).findEntry? key = none := by
  rfl

theorem LinkedEntry.run?_of_matching_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = some (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store)) := by
  simp [LinkedEntry.run?, LinkedEntry.runExact?, finite, typesEqual]

theorem LinkedEntry.runExact?_of_matching_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = entry.elaborated.inputs.values) :
    entry.runExact? inputs fuel store = some (.core (Core.runStateful fuel
      (Core.State.initial entry.elaborated.core inputs store))) := by
  simp [LinkedEntry.runExact?, finite, typesEqual]

theorem LinkedEntry.run?_of_mismatched_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠
      entry.elaborated.inputs.values) :
    entry.run? inputs fuel store = none := by
  simp [LinkedEntry.run?, LinkedEntry.runExact?, mismatch]

theorem LinkedEntry.runExact?_of_mismatched_types (entry : LinkedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠
      entry.elaborated.inputs.values) :
    entry.runExact? inputs fuel store = none := by
  simp [LinkedEntry.runExact?, mismatch]

@[simp] theorem link_budgetExhausted (program : CheckedProgram) (plan : Plan)
    (next : SpecializationKey)
    (pending : List SourceSpecializationWorklist.Request) :
    link program (.budgetExhausted plan next pending) =
      .error (.budgetExhausted next pending.length) := by
  rfl

@[simp] theorem linkWithStagingFuel_budgetExhausted
    (program : CheckedProgram) (plan : Plan) (next : SpecializationKey)
    (pending : List SourceSpecializationWorklist.Request) (fuel : Nat) :
    linkWithStagingFuel program (.budgetExhausted plan next pending) fuel =
      .error (.budgetExhausted next pending.length) := by
  rfl

@[simp] theorem link_eq_linkWithStagingFuel_default
    (program : CheckedProgram)
    (outcome : SourceSpecializationWorklist.Outcome) :
    link program outcome = linkWithStagingFuel program outcome 1024 := by
  rfl

end Solcore.Frontend.SourceCoreDirectLinking
