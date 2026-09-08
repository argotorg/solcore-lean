import Solcore.Frontend.TypedLetReturnBody
import Solcore.Frontend.TypedLetReturnBodyEvaluation
import Solcore.Frontend.TerminalReturnTreeEvaluationProperties

/-! Raw paths retain their stores and have unique values and costs without
checking. Typed existence uses the actual initial environment and extends it
only with the value obtained by evaluating the original initializer. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem TypedLetReturnBodyEvaluates.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    finalStore = initialStore := by
  induction evaluation with
  | terminal child => exact child.store_eq
  | binding initializer _ ih => exact ih.trans initializer.store_eq

theorem TypedLetReturnBodyEvaluates.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block}
    {left right : Core.Value} {leftStore rightStore : Core.Store}
    (first : TypedLetReturnBodyEvaluates owner table environment initialStore body left leftStore)
    (second : TypedLetReturnBodyEvaluates owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | terminal child =>
      cases second with
      | terminal other => exact child.deterministic other
      | binding _ _ => cases child with | single returned => cases returned
  | binding initializer _ ih =>
      cases second with
      | terminal other => cases other with | single returned => cases returned
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := initializer.deterministic otherInitializer
          exact ih otherTail

theorem TypedLetReturnBodyHasType.evaluates
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) (store : Core.Store) :
    ∃ value, TypedLetReturnBodyEvaluates owner inputs.names environment store body value store ∧
      Core.ValueHasType value type := by
  induction typing generalizing environment with
  | terminal child =>
      obtain ⟨value, evaluation, typed⟩ := child.evaluates sameIds environmentTyped store
      exact ⟨value, .terminal evaluation, typed⟩
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

theorem TypedLetReturnBodyEvaluates.preserves_type
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {type : Core.Ty}
    {value : Core.Value} {initialStore finalStore : Core.Store}
    (evaluation : TypedLetReturnBodyEvaluates owner inputs.names environment initialStore body value finalStore)
    (typing : TypedLetReturnBodyHasType types owner inputs body type)
    (sameIds : Resolved.LocalScope.ids environment = Resolved.LocalScope.ids inputs.context)
    (environmentTyped : Core.EnvironmentHasTypes
      (Resolved.LocalScope.values environment) (Resolved.LocalScope.values inputs.context)) :
    Core.ValueHasType value type ∧ finalStore = initialStore := by
  obtain ⟨other, evaluated, typed⟩ := typing.evaluates sameIds environmentTyped initialStore
  obtain ⟨rfl, sameStore⟩ := evaluation.deterministic evaluated
  exact ⟨typed, sameStore⟩

theorem TypedLetReturnBodyEvaluatesWithCost.erase
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore := by
  induction evaluation with
  | terminal child => exact .terminal child.erase
  | binding initializer _ ih => exact .binding initializer.erase ih

theorem TypedLetReturnBodyEvaluates.exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore) :
    ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost := by
  induction evaluation with
  | terminal child =>
      obtain ⟨cost, costed⟩ := child.exists_cost
      exact ⟨cost, .terminal costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, initializerCost⟩ := initializer.exists_cost
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding initializerCost tailCost⟩

theorem typedLetReturnBodyEvaluates_iff_exists_cost
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    TypedLetReturnBodyEvaluates owner table environment initialStore body value finalStore ↔
      ∃ cost, TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost :=
  ⟨TypedLetReturnBodyEvaluates.exists_cost, fun ⟨_, evaluation⟩ => evaluation.erase⟩

theorem TypedLetReturnBodyEvaluatesWithCost.store_eq
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    finalStore = initialStore := evaluation.erase.store_eq

theorem TypedLetReturnBodyEvaluatesWithCost.cost_pos
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body value finalStore cost) :
    0 < cost := by
  cases evaluation with
  | terminal child => exact child.cost_pos
  | binding _ _ => omega

theorem TypedLetReturnBodyEvaluatesWithCost.deterministic
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body left leftStore leftCost)
    (second : TypedLetReturnBodyEvaluatesWithCost owner table environment initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | terminal child =>
      cases second with
      | terminal other => exact child.deterministic other
      | binding _ _ => cases child with | single returned => cases returned
  | binding initializer _ ih =>
      cases second with
      | terminal other => cases other with | single returned => cases returned
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := initializer.deterministic otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
