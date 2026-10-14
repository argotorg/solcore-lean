import Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

theorem match_step (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchAt program registry size := by
  intro scope context environment before after resolution outcome control type caseFacts
    runtime covers locals heap scrutineeTyped casesTyped defaultTyped trace
  cases trace with
  | @scrutineeFault childSize scope context environment before after resolution actualFailure scrutinee =>
      have post := expressionIH childSize (Size.child_lt_stepSize (by simp))
        runtime covers locals heap scrutineeTyped scrutinee
      exact ⟨post.heap_typed, post.heap_extends, by intro value equal; cases equal⟩
  | @patternFault childSize scope context environment before middle hidden resolution node value location
      contains scrutinee allocated invalid =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated), by intro result equal; cases equal⟩
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticBinders, staticArmContext, staticFinal, armFacts,
        bindingsTyped, bindersEq, staticExtended, armTyped, monomorphic⟩ :=
        selected.armPreserves casesTyped (valueTyped.mono hiddenExtends)
      have exactExtended : BindersExtend scope.source.owner context (bindings.map Prod.fst) staticArmContext :=
        bindersEq.symm ▸ staticExtended
      have sameContext := Solcore.SourceSemantics.Dynamic.BindersExtend.functional extended exactExtended
      subst staticArmContext
      have valuesTyped : ValuesHaveTypes context hidden (bindings.map Prod.snd)
          ((bindings.map Prod.fst).map fun binder => binder.scheme.body) := by
        simpa only [List.map_map, Function.comp_def] using bindingsTyped.unzip
      have boundTyped := allocated.preservesHeapTyping hiddenTyped valuesTyped
      have boundExtends := allocated.extendsHeapTypes
      have armLocals := allocated.preservesEnvironmentAgreement exactExtended
        (fun binder member => monomorphic binder (bindersEq ▸ member))
        (locals.mono (firstExtends.trans hiddenExtends))
      have fields := Solcore.SourceSemantics.Dynamic.BindersExtend.runtimeContextFields extended
      have armClosed := fields.targetClosed runtime.closed
      have boundAtArm := boundTyped.transportClosed fields.signatures runtime.closed armClosed
        runtime.variables_closed (fields.targetResidualVariablesOpen runtime.residual_variables_open)
      have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        (runtime.transport fields) (fields.covers covers) armLocals boundAtArm armTyped body
      exact ⟨bodyPost.heap_typed.transportClosed fields.signatures.symm armClosed runtime.closed
        (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open,
        firstExtends.trans (hiddenExtends.trans (boundExtends.trans bodyPost.heap_extends)), by
          intro result equal
          have returned : outcome = .returned result := by cases outcome <;> simp_all [BodyOutcome.restore]
          exact (bodyPost.returned (by simp) result returned).transportClosed fields.signatures.symm armClosed runtime.closed
            (fields.targetVariablesClosed runtime.variables_closed) runtime.residual_variables_open⟩
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticFinal, facts, bodyTyped⟩ := defaultTyped statements selected.defaultBody_eq
      have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp))
        runtime covers (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped bodyTyped body
      exact ⟨bodyPost.heap_typed, firstExtends.trans (hiddenExtends.trans bodyPost.heap_extends), by
          intro result equal
          have returned : outcome = .returned result := by cases outcome <;> simp_all [BodyOutcome.restore]
          exact bodyPost.returned (by simp) result returned⟩
  | @noBranch childSize scope context environment before middle hidden resolution node value location contains scrutinee allocated _selected =>
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
          (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      exact ⟨middleTyped.allocate (.some (sameType ▸ valueTyped)) allocated,
        firstExtends.trans (HeapTypesExtend.of_allocation allocated), by intro result equal; cases equal⟩

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
