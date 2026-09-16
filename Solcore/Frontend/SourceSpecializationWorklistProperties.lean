import Solcore.Frontend.SourceSpecializationWorklist

/-! Small checked laws for finite specialization-worklist boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceSpecializationWorklist

@[simp] theorem run_empty (program : CheckedProgram) (budget : Nat) :
    run program [] budget = .ok (.complete {
      seedKeys := []
      specializations := []
      callEdges := []
    }) := by
  cases budget <;> rfl

theorem run_zero_single (program : CheckedProgram) (request : Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (resolved : resolveRequest program request = .ok specialized) :
    run program [request] 0 = .ok (.budgetExhausted {
      seedKeys := [specialized.key]
      specializations := []
      callEdges := []
    } specialized.key [request]) := by
  simp [run, canonicalSeedKeys, runAux, nextUnseen, resolved]
  rfl

end Solcore.Frontend.SourceSpecializationWorklist
