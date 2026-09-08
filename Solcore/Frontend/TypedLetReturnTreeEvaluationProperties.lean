import Solcore.Frontend.TypedLetReturnTree
import Solcore.Frontend.TypedLetReturnTreeEvaluation

/-! Raw store/value/cost laws require no checking or runtime type assumptions.
Whole typing gives existence only with an actual aligned, typed environment;
each strict initializer supplies the real value used in its extended tail. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnTreeEvaluates.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | single child => exact child.store_eq
  | binding child _ ih | ifTrue child _ ih | ifFalse child _ ih => exact ih.trans child.store_eq

theorem TypedLetReturnTreeEvaluates.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TypedLetReturnTreeEvaluates owner table environment initialStore body left leftStore)
    (second : TypedLetReturnTreeEvaluates owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | binding _ _ | ifTrue _ _ | ifFalse _ _ => cases child
  | binding initializer _ ih =>
      cases second with
      | single other => cases other
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializer.deterministic otherInitializer
          exact ih otherTail
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ => cases (condition.deterministic otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ => cases (condition.deterministic otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := condition.deterministic otherCondition
          exact ih otherBranch

theorem TypedLetReturnTreeHasType.evaluates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) (store : Core.Store) :
    ∃ value, TypedLetReturnTreeEvaluates owner inputs.names environment store body value store ∧
      Core.ValueHasType value type := by
  induction typing generalizing environment with
  | single child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .single evaluation, typed⟩
  | @binding inputs blockSpan letSpan name annotation initializer rest declaredType returnType
      _ _ initializerTyping _ ih =>
      obtain ⟨boundValue, initializerEvaluation, boundTyped⟩ :=
        initializerTyping.evaluates sameIds environmentTyped store
      have tailIds : Resolved.LocalScope.ids
          ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment) =
          Resolved.LocalScope.ids (inputs.bindFresh owner name.value declaredType).context := by
        simpa only [LocalTypeInputs.bindFresh_context, Resolved.LocalScope.ids, List.map_cons, Prod.fst]
          using congrArg (Resolved.freshLocalId owner inputs.ids :: ·) sameIds
      have tailTyped : Core.EnvironmentHasTypes
          (Resolved.LocalScope.values ((Resolved.freshLocalId owner inputs.ids, boundValue) :: environment))
          (Resolved.LocalScope.values (inputs.bindFresh owner name.value declaredType).context) :=
        .cons boundTyped environmentTyped
      obtain ⟨value, tailEvaluation, valueTyped⟩ := ih tailIds tailTyped
      refine ⟨value, .binding initializerEvaluation ?_, valueTyped⟩
      simpa only [LocalTypeInputs.bindFresh_names, LocalTypeInputs.names_ids] using tailEvaluation
  | conditional conditionTyping _ _ thenIH elseIH =>
      obtain ⟨conditionValue, conditionEvaluation, conditionTyped⟩ :=
        conditionTyping.evaluates sameIds environmentTyped store
      obtain ⟨choice, rfl⟩ := conditionTyped.bool_shape
      cases choice with
      | false =>
          obtain ⟨value, evaluation, typed⟩ := elseIH sameIds environmentTyped
          exact ⟨value, .ifFalse conditionEvaluation evaluation, typed⟩
      | true =>
          obtain ⟨value, evaluation, typed⟩ := thenIH sameIds environmentTyped
          exact ⟨value, .ifTrue conditionEvaluation evaluation, typed⟩

theorem TypedLetReturnTreeEvaluates.preserves_type
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TypedLetReturnTreeEvaluates owner inputs.names environment initialStore body value finalStore)
    (typing : TypedLetReturnTreeHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TypedLetReturnTreeEvaluatesWithCost.erase
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | single child => exact .single child.erase
  | binding initializer _ ih => exact .binding initializer.erase ih
  | ifTrue condition _ ih => exact .ifTrue condition.erase ih
  | ifFalse condition _ ih => exact .ifFalse condition.erase ih

theorem TypedLetReturnTreeEvaluates.exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore) :
    ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | single child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .single costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, initializerCost⟩ := initializer.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding initializerCost tailCost⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue conditionCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, conditionCost⟩ := condition.exists_cost
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse conditionCost branchCost⟩

theorem typedLetReturnTreeEvaluates_iff_exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnTreeEvaluates owner table environment initialStore body value finalStore ↔
      ∃ cost, TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost :=
  ⟨TypedLetReturnTreeEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TypedLetReturnTreeEvaluatesWithCost.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TypedLetReturnTreeEvaluatesWithCost.cost_pos
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | single child => exact child.cost_pos
  | binding _ _ | ifTrue _ _ | ifFalse _ _ => omega

theorem TypedLetReturnTreeEvaluatesWithCost.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body left leftStore leftCost)
    (second : TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | single child =>
      cases second with
      | single other => exact child.deterministic other
      | binding _ _ | ifTrue _ _ | ifFalse _ _ => cases child
  | binding initializer _ ih =>
      cases second with
      | single other => cases other
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | ifTrue condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (condition.deterministic otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | single other => cases other
      | ifTrue otherCondition _ => cases (condition.deterministic otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := condition.deterministic otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
