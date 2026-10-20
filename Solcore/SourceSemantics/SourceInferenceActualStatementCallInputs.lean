import Solcore.SourceSemantics.SourceInferenceActualCallProperties
import Solcore.SourceSemantics.SourceInferenceActualMatchPrefixProperties
import Solcore.SourceSemantics.SourceInferenceGeneralizationLifetimeBranchSteps

/-! Each statement child receives inputs from its actual preceding calls. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceExecution
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness.ProtectedVariables

private theorem statementAllocation_inputs {initial allocated : State} {id : StatementId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (allocation : initial.allocateStatementId = (id, allocated)) :
    allocated.InferenceReady ∧ allocated.RequirementsWellFormed ∧ allocated.inference.next = initial.inference.next := by
  have same : allocated = initial.allocateStatementId.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨ready.allocateStatementId, wellFormed, rfl⟩

private theorem hiddenAllocation_inputs {initial allocated : State} {id : Resolved.LocalId}
    (ready : initial.InferenceReady) (wellFormed : initial.RequirementsWellFormed)
    (allocation : initial.allocateHiddenLocal = (id, allocated)) :
    allocated.InferenceReady ∧ allocated.RequirementsWellFormed ∧ allocated.inference.next = initial.inference.next := by
  have same : allocated = initial.allocateHiddenLocal.2 := (congrArg Prod.snd allocation).symm
  subst allocated
  exact ⟨ready.allocateHiddenLocal, wellFormed, rfl⟩

namespace ChildStep

theorem inputs_statement
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {expected : Ty} {initial : State} {result : StatementResult} {child : CallIndex}
    (inputs : (CallIndex.statement fuel context source expected initial result).Inputs)
    (step : ChildStep (.statement fuel context source expected initial result) child) : child.Inputs := by
  have returnBound : expected.VariablesBelow initial.inference.next := inputs.bounds
  cases step with
  | statement_initializer _ _ allocation annotation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      cases annotation with
      | absent => simp [CallIndex.InputBounds]
      | present accepted => intro type member; cases member; exact resolveSourceType_success_variablesBelow accepted _
  | statement_return _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member
      cases member
      exact allocated.2.2 ▸ returnBound
  | statement_expression _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | statement_block _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by change expected.VariablesBelow _; exact allocated.2.2 ▸ returnBound⟩
  | statement_if_condition _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_if_then _ _ allocation conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1,
        inputs.catalog, (allocated.2.2 ▸ returnBound).weaken condition.1.next_le⟩
  | statement_if_else _ _ allocation conditionAccepted _ thenAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      have returnBelow := (allocated.2.2 ▸ returnBound).weaken condition.1.next_le
      have thenProperties := inferStatementsFuel_inferenceProperties condition.2.1 inputs.catalog.formation inputs.catalog.canonical returnBelow thenAccepted
      exact ⟨(State.restoreLexicalScope_inferenceProperties condition.2.1 thenProperties.1).2,
        (inferStatementsFuel_direct_progress thenAccepted).wellFormed
          ((inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1),
        inputs.catalog, returnBelow.weaken thenProperties.1.next_le⟩
  | statement_assignment _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_bitnot _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_while_condition _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      refine ⟨allocated.1, allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_while_body _ _ allocation conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have condition := inferExprFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed allocated.2.1,
        inputs.catalog.withLoopDepth _, (allocated.2.2 ▸ returnBound).weaken condition.1.next_le⟩
  | statement_for_initializer _ _ allocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_for_condition _ _ allocation initializerAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      refine ⟨initialized.2, (inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1, inputs.catalog, ?_⟩
      intro type member; cases member; exact Ty.variablesBelow_constructor _ _
  | statement_for_body _ _ allocation initializerAccepted conditionAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      have condition := inferExprFuel_inferenceProperties initialized.2 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      exact ⟨condition.2.1, (inferExprFuel_direct_progress conditionAccepted).wellFormed
        ((inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1),
        inputs.catalog.withLoopDepth _, (allocated.2.2 ▸ returnBound).weaken (initialized.1.trans condition.1).next_le⟩
  | statement_for_post _ _ allocation initializerAccepted conditionAccepted bodyAccepted _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have initialized := inferForItemsFuel_inferenceProperties allocated.1 inputs.catalog.formation inputs.catalog.canonical initializerAccepted
      have condition := inferExprFuel_inferenceProperties initialized.2 inputs.catalog.formation inputs.catalog.canonical
        (by intro type member; cases member; exact Ty.variablesBelow_constructor _ _) conditionAccepted
      have bodyProperties := inferStatementsFuel_inferenceProperties (context := {context with loopDepth := context.loopDepth + 1}) condition.2.1 inputs.catalog.formation inputs.catalog.canonical
        ((allocated.2.2 ▸ returnBound).weaken (initialized.1.trans condition.1).next_le) bodyAccepted
      exact ⟨(State.restoreLexicalScope_inferenceProperties initialized.2 (condition.1.trans bodyProperties.1)).2,
        (inferStatementsFuel_direct_progress bodyAccepted).wellFormed ((inferExprFuel_direct_progress conditionAccepted).wellFormed
          ((inferForItemsFuel_direct_progress initializerAccepted).wellFormed allocated.2.1)),
        inputs.catalog.withLoopDepth _, trivial⟩
  | statement_match_single _ _ allocation _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, by simp [CallIndex.InputBounds]⟩
  | statement_match_many _ _ allocation _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      exact ⟨allocated.1, allocated.2.1, inputs.catalog, trivial⟩
  | statement_match_cases _ _ allocation scrutineeAccepted hiddenAllocation _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have scrutinee := matchScrutinee_properties allocated.1 inputs.catalog scrutineeAccepted
      have hidden := hiddenAllocation_inputs scrutinee.2.1
        (matchScrutinee_wellFormed allocated.2.1 scrutineeAccepted) hiddenAllocation
      exact ⟨hidden.1, hidden.2.1, inputs.catalog, hidden.2.2 ▸ scrutinee.2.2,
        hidden.2.2 ▸ (allocated.2.2 ▸ returnBound).weaken scrutinee.1.next_le, rfl⟩
  | statement_match_default _ _ allocation scrutineeAccepted hiddenAllocation casesAccepted _ _ =>
      have allocated := statementAllocation_inputs inputs.ready inputs.wellFormed allocation
      have scrutinee := matchScrutinee_properties allocated.1 inputs.catalog scrutineeAccepted
      have hidden := hiddenAllocation_inputs scrutinee.2.1
        (matchScrutinee_wellFormed allocated.2.1 scrutineeAccepted) hiddenAllocation
      have returnBelow := hidden.2.2 ▸ (allocated.2.2 ▸ returnBound).weaken scrutinee.1.next_le
      have casesProperties := inferMatchCasesFuel_inferenceProperties hidden.1 inputs.catalog.formation inputs.catalog.canonical
        (hidden.2.2 ▸ scrutinee.2.2) returnBelow rfl casesAccepted
      exact ⟨casesProperties.2.1, (inferMatchCasesFuel_direct_progress casesAccepted).wellFormed hidden.2.1,
        inputs.catalog, returnBelow.weaken casesProperties.1.next_le⟩

end ChildStep
end Solcore.SourceSemantics.SourceInferenceExecution
