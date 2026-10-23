import Solcore.SourceSemantics.SourceInferenceActualGeneralizationInference
import Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorCalls
import Solcore.SourceSemantics.SourceInferenceActualLocalAllocatorSuffix

/-! An actual inference segment bounds both retained input reads and the
lookups it executes by its resulting local allocator. -/
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail

def LocalReadCutoff (state : State) : Prop :=
  ∀ node : ExpressionNode, .expression node ∈ state.nodes →
    ∀ name binder, node.form = .reference name (.local binder) →
      binder.binderIndex < state.nextLocal

namespace CallIndex

/-- The same eleven-family traversal can be rooted at this accepted segment. -/
theorem relativeReadProgress {call : CallIndex} (accepted : call.Accepted) :
    ActualGeneralization.RelativeReadProgress call call.initial call.final := by
  cases call <;> first
  | exact ActualGeneralization.inferExprFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferConstructorApplicationFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferConstructorArgumentsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferStatementsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferStatementFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferForItemsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferForItemFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferPlaceFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferAssignedValueFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferExprsFuel_relative_read_progress accepted (.root accepted)
  | exact ActualGeneralization.inferMatchCasesFuel_relative_read_progress accepted (.root accepted)

/-- An old reference keeps its target; a new lookup lies inside this call's
actual allocator interval. Neither alternative assumes a later checkpoint. -/
theorem localReadCutoff {call : CallIndex} (accepted : call.Accepted)
    (inputs : call.Inputs) (below : call.initial.LocalBindersBelowNextLocal)
    (allocated : call.initial.DirectRequirementsAllocated)
    (previous : LocalReadCutoff call.initial) : LocalReadCutoff call.final := by
  have relative := (relativeReadProgress accepted).calls inputs.wellFormed allocated
    (RelativeLocalRead.Origins.initial call.initial.nodes)
  intro node member name binder form
  rcases relative node member name binder form with old | current
  · obtain ⟨original, present, _, sameForm⟩ := old
    exact Nat.lt_of_lt_of_le
      (previous original present name binder (sameForm.symm.trans form)) (call.local_next accepted)
  · obtain ⟨lookup, _, sameForm, here, present⟩ := current.active
    have sameBinder : binder = lookup.binder.id := by
      exact ReferenceResolution.local.inj (ExpressionForm.reference.inj (form.symm.trans sameForm)).2
    have localBound := ActualLocalAllocator.occurrence_bound inputs below here lookup.binder present
    have interval := here.local_interval
    have advanced := (ActualLocalRead.lookupCall lookup).local_next here.accepted
    rw [sameBinder]
    exact Nat.lt_of_lt_of_le localBound (Nat.le_trans advanced interval.2)

theorem directRequirementsAllocated {call : CallIndex} (accepted : call.Accepted)
    (wellFormed : call.initial.RequirementsWellFormed)
    (allocated : call.initial.DirectRequirementsAllocated) :
    call.final.DirectRequirementsAllocated :=
  (relativeReadProgress accepted).reads.ledger.allocated wellFormed allocated

end CallIndex
end Solcore.SourceSemantics.SourceInferenceExecution
