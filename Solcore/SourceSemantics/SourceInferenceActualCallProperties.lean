import Solcore.SourceSemantics.SourceInferenceActualCallGraph
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeContinuation

/-! Allocator and formation inputs are indexed by the exact inference call.
They describe ordinary checker state, with no initializer or semantic law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables
namespace CallIndex

def context : CallIndex → SourceInference.Context
  | .expression _ context _ _ _ _ _
  | .constructorApplication _ context _ _ _ _ _ _ _ _
  | .constructorArguments _ context _ _ _ _ _
  | .statements _ context _ _ _ _
  | .statement _ context _ _ _ _
  | .forItems _ context _ _ _
  | .forItem _ context _ _ _ _
  | .place _ context _ _ _ _
  | .assignedValue _ context _ _ _ _ _ _ _
  | .expressions _ context _ _ _ _
  | .matchCases _ context _ _ _ _ _ _ => context

def InputBounds : CallIndex → Prop
  | .expression _ _ _ expected initial _ _ =>
      ∀ type ∈ expected, type.VariablesBelow initial.inference.next
  | .constructorApplication _ _ _ _ instantiation _ expected initial _ _ =>
      (∀ type ∈ instantiation.payloadTypes, type.VariablesBelow initial.inference.next) ∧
      instantiation.resultType.VariablesBelow initial.inference.next ∧
      ∀ type ∈ expected, type.VariablesBelow initial.inference.next
  | .constructorArguments _ _ _ expectedTypes initial _ _ =>
      ∀ type ∈ expectedTypes, type.VariablesBelow initial.inference.next
  | .statements _ _ _ expectedReturn initial _
  | .statement _ _ _ expectedReturn initial _ => expectedReturn.VariablesBelow initial.inference.next
  | .matchCases _ _ scrutinee expectedReturn saved _ initial _ =>
      scrutinee.VariablesBelow initial.inference.next ∧
      expectedReturn.VariablesBelow initial.inference.next ∧ initial.lexicalScope = saved
  | _ => True

def outputTypes : CallIndex → List Ty
  | .expression _ _ _ _ _ value _
  | .constructorApplication _ _ _ _ _ _ _ _ value _ => [value.type]
  | .constructorArguments _ _ _ _ _ values _
  | .expressions _ _ _ _ values _ => values.map (·.type)
  | .statements _ _ _ _ _ result => [result.type]
  | .statement _ _ _ _ _ result => [result.type]
  | .place _ _ _ _ value _ => [value.type]
  | .assignedValue _ _ _ _ _ _ assignment value _ => [assignment.target.type, value.type]
  | _ => []

structure Inputs (call : CallIndex) : Prop where
  ready : call.initial.InferenceReady
  wellFormed : call.initial.RequirementsWellFormed
  catalog : LifetimeInferenceContext call.context
  bounds : call.InputBounds

theorem Inputs.progress {call : CallIndex} (inputs : call.Inputs) (accepted : call.Accepted) :
    call.initial.InferenceProgress call.final ∧ call.final.InferenceReady ∧
      ∀ type ∈ call.outputTypes, type.VariablesBelow call.final.inference.next := by
  cases call with
  | expression fuel context source expected initial value final =>
      have facts := inferExprFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds accepted
      exact ⟨facts.1, facts.2.1, fun type member => (List.mem_singleton.mp member) ▸ facts.2.2⟩
  | constructorApplication fuel context source id instantiation arguments expected initial value final =>
      have facts := inferConstructorApplicationFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical
        inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 accepted
      exact ⟨facts.1, facts.2.1, fun type member => (List.mem_singleton.mp member) ▸ facts.2.2⟩
  | constructorArguments fuel context sources expected initial values final =>
      have facts := inferConstructorArgumentsFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds accepted
      refine ⟨facts.1, facts.2.1, ?_⟩
      intro type member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      exact facts.2.2 value present
  | statements fuel context sources expected initial result =>
      have facts := inferStatementsFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds accepted
      exact ⟨facts.1, facts.2.1, fun type member => (List.mem_singleton.mp member) ▸ facts.2.2⟩
  | statement fuel context source expected initial result =>
      have facts := inferStatementFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical inputs.bounds accepted
      exact ⟨facts.1, facts.2.1, fun type member => (List.mem_singleton.mp member) ▸ facts.2.2⟩
  | forItems fuel context sources initial result =>
      have facts := inferForItemsFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical accepted
      exact ⟨facts.1, facts.2, by simp [outputTypes]⟩
  | forItem fuel context source initial value final =>
      have facts := inferForItemFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical accepted
      exact ⟨facts.1, facts.2, by simp [outputTypes]⟩
  | place fuel context source initial value final =>
      have facts := inferPlaceFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical accepted
      exact ⟨facts.1, facts.2.1, fun type member => (List.mem_singleton.mp member) ▸ facts.2.2⟩
  | assignedValue fuel context target operator value initial assignment inferred final =>
      have facts := inferAssignedValueFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical accepted
      refine ⟨facts.1, facts.2.1, ?_⟩
      intro type member
      rcases List.mem_cons.mp member with rfl | member
      · exact facts.2.2.1
      · exact (List.mem_singleton.mp member) ▸ facts.2.2.2
  | expressions fuel context sources initial values final =>
      have facts := inferExprsFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical accepted
      refine ⟨facts.1, facts.2.1, ?_⟩
      intro type member
      obtain ⟨value, present, rfl⟩ := List.mem_map.mp member
      exact facts.2.2 value present
  | matchCases fuel context scrutinee expected saved cases initial result =>
      have facts := inferMatchCasesFuel_inferenceProperties inputs.ready inputs.catalog.formation inputs.catalog.canonical
        inputs.bounds.1 inputs.bounds.2.1 inputs.bounds.2.2 accepted
      exact ⟨facts.1, facts.2.1, by simp [outputTypes]⟩

theorem Inputs.resultWellFormed {call : CallIndex} (inputs : call.Inputs) (accepted : call.Accepted) :
    call.final.RequirementsWellFormed := by
  cases call <;> first
  | exact (inferExprFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferConstructorApplicationFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferConstructorArgumentsFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferStatementsFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferStatementFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferForItemsFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferForItemFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferPlaceFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferAssignedValueFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferExprsFuel_direct_progress accepted).wellFormed inputs.wellFormed
  | exact (inferMatchCasesFuel_direct_progress accepted).wellFormed inputs.wellFormed

end CallIndex
end Solcore.SourceSemantics.SourceInferenceExecution
