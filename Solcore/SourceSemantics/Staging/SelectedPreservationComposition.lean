import Solcore.SourceSemantics.Staging.SelectedPreservationContracts
import Solcore.SourceSemantics.Staging.SelectedFaultPreservationApplies

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem OutcomePreserved.success {context : Context} {before after : Heap}
    {type : Ty} {value : Value} (post : OutcomePreserved context before after type (.value value)) :
    ExpressionEvaluationPreserved context before after value type :=
  ⟨post.value_typed value rfl, post.heap_typed, post.heap_extends⟩

theorem StatementsAt.bodySuccess {size : Nat} (sound : StatementsAt program registry size) :
    BodySuccessAt program registry size := by
  intro scope context staticFinal runtimeFinal environment before after roots facts type outcome value
    runtime covers locals heap typed completes trace result
  have preserved := sound runtime covers locals heap typed trace
  cases result with
  | returned => exact ⟨preserved.returned (fun _ => completes) _ rfl, preserved.heap_typed, preserved.heap_extends⟩
  | unit => exact ⟨.unit, preserved.heap_typed, preserved.heap_extends⟩

theorem StatementsAt.fault {size : Nat} (sound : StatementsAt program registry size) :
    FaultPreservation.StatementsAt program registry size := by
  intro mode scope context staticFinal runtimeFinal environment before after statements failure control facts
    runtime covers locals heap typed trace
  have preserved := sound runtime covers locals heap typed trace
  exact ⟨preserved.heap_typed, preserved.heap_extends⟩

theorem applies_all_step (selectedBodies : GlobalBodiesTyped program registry) (size : Nat)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    AppliesAt program registry size := by
  intro scope context source before after callable arguments packed outcome parameter result
    runtime heap typed packing packedTyped trace
  cases outcome with
  | value value =>
    have preserved := applies_step selectedBodies size
      (fun smaller below => StatementsAt.bodySuccess (statementsIH smaller below))
      runtime heap typed packing packedTyped trace
    exact ⟨preserved.heap_typed, preserved.heap_extends, by
      intro actual equal; cases equal; exact preserved.value_typed⟩
  | fault failure =>
    have preserved := SelectedFaultPreservation.applies_step selectedBodies size
      (fun smaller below => StatementsAt.fault (statementsIH smaller below))
      runtime heap typed packing packedTyped trace
    exact ⟨preserved.1, preserved.2, by intro value equal; cases equal⟩

theorem expressions_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (expressionsIH : ∀ smaller, smaller < size → ExpressionsAt program registry smaller) :
    ExpressionsAt program registry size := by
  intro scope context environment before after ids outcome types runtime covers locals heap typed trace
  cases trace with
  | nil =>
    cases typed
    exact ⟨heap, .refl _, by intro values equal; cases equal; exact .nil⟩
  | @cons headSize tailSize scope context environment before middle after id ids value values head tail =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      have next := expressionsIH tailSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, by
        intro actual equal; cases equal
        exact .cons ((first.value_typed _ rfl).mono next.heap_extends) (next.values_typed _ rfl)⟩
  | @headFault headSize scope context environment before after id ids failure head =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      exact ⟨first.heap_typed, first.heap_extends, by intro values equal; cases equal⟩
  | @tailFault headSize tailSize scope context environment before middle after id ids value failure head tail =>
    cases typed with
    | cons headTyped tailTyped =>
      have first := expressionIH headSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap headTyped head
      have next := expressionsIH tailSize (Size.child_lt_stepSize (by simp)) runtime covers
        (locals.mono first.heap_extends) first.heap_typed tailTyped tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, by intro values equal; cases equal⟩

theorem coercion_path_step (size : Nat)
    (stepIH : ∀ smaller, smaller < size → CoercionStepAt program registry smaller)
    (pathIH : ∀ smaller, smaller < size → CoercionPathAt program registry smaller) :
    CoercionPathAt program registry size := by
  intro scope context before after steps input outcome sourceType targetType runtime heap typed valid trace
  cases trace with
  | coercionsNil =>
    cases valid
    exact ⟨heap, .refl _, by intro value equal; cases equal; exact typed⟩
  | @coercionsCons headSize tailSize scope context before middle after step steps input converted outcome head tail =>
    cases valid with
    | cons headValid tailValid =>
      have first := stepIH headSize (Size.child_lt_stepSize (by simp)) runtime heap typed headValid head
      have next := pathIH tailSize (Size.child_lt_stepSize (by simp)) runtime
        first.heap_typed (first.value_typed _ rfl) tailValid tail
      exact ⟨next.heap_typed, first.heap_extends.trans next.heap_extends, next.value_typed⟩
  | @coercionsFault headSize scope context before after step steps input failure head =>
    cases valid with
    | cons headValid tailValid =>
      have first := stepIH headSize (Size.child_lt_stepSize (by simp)) runtime heap typed headValid head
      exact ⟨first.heap_typed, first.heap_extends, by intro value equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
