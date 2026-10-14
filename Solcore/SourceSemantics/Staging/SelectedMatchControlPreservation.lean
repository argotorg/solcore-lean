import Solcore.SourceSemantics.Staging.SelectedControlPreservationContracts
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic
variable {program : Program} {registry : Registry}

def MatchControlAt (program : Program) (registry : Registry) (size : Nat) : Prop :=
  ∀ {scope : Scope} {context : Context} {environment resultEnvironment : Dynamic.Environment}
    {before after : Heap} {resolution : MatchResolution} {outcome : BodyOutcome}
    {control : ControlContext} {facts : StatementFacts},
    SourceRuntimeValid program context scope.source → scope.evidence.Covers context →
    EnvironmentAgrees before context.locals environment → HeapWellTyped context before →
    StatementControlFormTyping scope.source control context (.matchWith resolution) facts →
    Size.Match program registry size scope context environment before resolution outcome after →
    outcome = .fallthrough resultEnvironment → facts.control.canFallthrough = true

theorem match_control_step (catalog : SignatureCatalogWellFormed program.signatures) (size : Nat)
    (expressionIH : ∀ smaller, smaller < size → ExpressionAt program registry smaller)
    (statementsIH : ∀ smaller, smaller < size → StatementsAt program registry smaller) :
    MatchControlAt program registry size := by
  intro scope context environment resultEnvironment before after resolution outcome control facts
    runtime covers locals heap controlTyped trace falls
  cases trace with
  | scrutineeFault | patternFault => cases falls
  | @arm childSize bodySize scope context armContext finalContext environment armEnvironment
      before middle hidden bound after resolution node value location statements bindings outcome
      contains scrutinee hiddenAllocated selected extended allocated body =>
      have common : ∃ scrutineeType caseFacts fallbackFacts summary,
          facts.control = summary.eraseValue ∧
          ExpressionHasType scope.source context resolution.scrutinee scrutineeType ∧
          MatchCasesHaveType scope.source control context scrutineeType resolution.cases caseFacts ∧
          mergeBodyControls caseFacts fallbackFacts = some summary := by
        cases controlTyped with
        | matchWithoutDefault _ scrutineeTyped casesTyped _ merged => exact ⟨_, _, none, _, rfl, scrutineeTyped, casesTyped, merged⟩
        | matchWithDefault _ scrutineeTyped casesTyped _ merged => exact ⟨_, _, some _, _, rfl, scrutineeTyped, casesTyped, merged⟩
      obtain ⟨scrutineeType, caseFacts, fallbackFacts, summary, summaryEq, scrutineeTyped, casesTyped, merged⟩ := common
      obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH _ (Size.child_lt_stepSize (by simp)))
        runtime covers locals heap scrutineeTyped scrutinee
      obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
      have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
        (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
      subst typedNode
      have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
      have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
      obtain ⟨staticBinders, staticArmContext, staticFinal, armFacts,
        bindingsTyped, bindersEq, staticExtended, armTyped, armMember, monomorphic⟩ :=
        selected.arm_preserves_typing casesTyped (valueTyped.mono hiddenExtends)
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
      have armFalls : armFacts.control.canFallthrough = true := by
        cases outcome with
        | fallthrough env => exact (bodyPost.fallthrough env rfl).2.2
        | returned | breaking | continuing | fault => cases falls
      rw [summaryEq]
      exact ControlSummary.eraseValue_canFallthrough
        (MergeBodyControls.allows_of_mem (outcome := .fallthrough environment) merged armMember armFalls)
  | @default childSize bodySize scope context finalContext environment before middle hidden after
      resolution node value location statements outcome contains scrutinee hiddenAllocated selected body =>
      cases controlTyped with
      | matchWithoutDefault absent _ _ _ _ =>
          have present := selected.defaultBody_eq
          rw [absent] at present
          contradiction
      | matchWithDefault present scrutineeTyped casesTyped defaultTyped merged =>
          have exactBody := selected.defaultBody_eq
          have sameBody := Option.some.inj (present.symm.trans exactBody)
          subst statements
          obtain ⟨valueTyped, middleTyped, firstExtends⟩ := expression_value (expressionIH childSize (Size.child_lt_stepSize (by simp)))
            runtime covers locals heap scrutineeTyped scrutinee
          obtain ⟨typedNode, typedContains, sameType⟩ := scrutineeTyped.stored_type
          have same := Option.some.inj ((lookupExpression?_complete runtime.graph.nodeOccurrencesUnique typedContains).symm.trans
            (lookupExpression?_complete runtime.graph.nodeOccurrencesUnique contains))
          subst typedNode
          have hiddenTyped := middleTyped.allocate (.some (sameType ▸ valueTyped)) hiddenAllocated
          have hiddenExtends := HeapTypesExtend.of_allocation hiddenAllocated
          have bodyPost := statementsIH bodySize (Size.child_lt_stepSize (by simp)) runtime covers
            (locals.mono (firstExtends.trans hiddenExtends)) hiddenTyped defaultTyped body
          have defaultFalls := by
            cases outcome with
            | fallthrough env => exact (bodyPost.fallthrough env rfl).2.2
            | returned | breaking | continuing | fault => cases falls
          exact ControlSummary.eraseValue_canFallthrough
            (MergeBodyControls.allows_of_fallback (outcome := .fallthrough environment) merged defaultFalls)
  | @noBranch childSize scope context environment before middle hidden resolution node value location contains scrutinee allocated selected =>
      cases controlTyped with
      | matchWithoutDefault absent scrutineeTyped casesTyped exhaustive _merged =>
          have typed := expressionIH childSize (Size.child_lt_stepSize (by simp)) runtime covers locals heap scrutineeTyped scrutinee
          rw [absent] at selected
          exact (selected.noBranch_impossible_of_exhaustive
            (by simpa [runtime.signatures] using catalog) casesTyped (typed.value_typed _ rfl) exhaustive).elim
      | matchWithDefault present _ _ _ _ =>
          have absent := selected.noBranch_defaultBody_eq
          rw [present] at absent
          contradiction

end Solcore.SourceSemantics.Staging.Recursive.SelectedPreservation
