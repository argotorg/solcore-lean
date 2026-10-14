import Solcore.SourceSemantics.Staging.SelectedAtomicPreservation
import Solcore.SourceSemantics.Staging.SelectedPreservationProjections
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem raw_form_step (size : Nat)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller)
    (appliesIH : ∀ smaller, smaller < size → AppliesAt program registry smaller) :
    RawFormAt program registry size := by
  intro scope context environment before after form requirements coercions outcome rawType finalType plan
    runtime covers locals heap occurrence typed _valid trace
  cases trace with
  | rawAtomicValue atomic valueRule =>
      have post := atomic_value runtime covers locals heap occurrence typed atomic valueRule
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal; exact post.value_typed⟩
  | rawAtomicFault atomic faultRule =>
      have same := FaultPreservation.atomic_fault_heap atomic faultRule
      subst after
      exact ⟨heap, .refl _, by intro value equal; cases equal⟩
  | @rawDirectArgumentsFault childrenSize scope context environment before after callee arguments instantiation name failure requirements coercions _calleeOccurrence children =>
      cases typed with
      | directCall _calleeTyped _application argumentsTyped =>
          have post := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @rawDirectApplied childrenSize invocationSize scope context environment before argumentsHeap after callee arguments instantiation name values evidence outcome requirements coercions _calleeOccurrence valid children callEvidence invocation =>
      cases typed with
      | @directCall _ callee arguments instantiation parameterTypes resultType predicates _calleeTyped application argumentsTyped =>
          have args := expressionsIH childrenSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap argumentsTyped children
          cases application with
          | intro _signature _admissible _declaration _parameters _result functionType _predicates =>
              cases callEvidence with
              | intro _coercions _requirements produces =>
                  have calleeTyped : ValueHasType context argumentsHeap (.global ⟨instantiation, evidence⟩)
                      (.function (Ty.productMany parameterTypes) rawType) := by
                    rw [← functionType]
                    exact .global valid ⟨produces.valid, by
                      intro predicate member
                      exact produces.supplies predicate member⟩
                  obtain ⟨packed, packing⟩ := ValuesPack.exists_pack values
                  have argumentTyped := packing.hasType (args.values_typed _ rfl)
                  have post := appliesIH invocationSize (Size.child_lt_stepSize (by simp))
                    runtime args.heap_typed calleeTyped packing argumentTyped invocation
                  exact ⟨post.heap_typed, args.heap_extends.trans post.heap_extends, post.value_typed⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
