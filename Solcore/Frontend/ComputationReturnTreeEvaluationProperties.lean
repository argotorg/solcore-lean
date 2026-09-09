import Solcore.Frontend.ComputationReturnTreeEvaluation

/-! Child laws lift through original mixed-body constructors. Raw cost
existence and joint determinism remain independent of checking and typing. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem erase_cost
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat}
    (evaluation : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body value finalStore cost) :
    ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore := by
  induction evaluation with
  | bare => exact .bare
  | expression child => exact .expression (childCostIff.mpr ⟨_, child⟩)
  | block _ ih => exact .block ih
  | binding initializer _ ih =>
      exact .binding (childCostIff.mpr ⟨_, initializer⟩) ih
  | inferred initializer _ ih =>
      exact .inferred (childCostIff.mpr ⟨_, initializer⟩) ih
  | discard expression _ ih =>
      exact .discard (childCostIff.mpr ⟨_, expression⟩) ih
  | ifTrue condition _ ih =>
      exact .ifTrue (childCostIff.mpr ⟨_, condition⟩) ih
  | ifFalse condition _ ih =>
      exact .ifFalse (childCostIff.mpr ⟨_, condition⟩) ih

private theorem cost_exists
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value}
    (evaluation : ComputationReturnTreeEvaluates ChildEval owner table environment
      initialStore body value finalStore) :
    ∃ cost, ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body value finalStore cost := by
  induction evaluation with
  | bare => exact ⟨1, .bare⟩
  | expression child =>
      obtain ⟨_, costed⟩ := childCostIff.mp child
      exact ⟨_, .expression costed⟩
  | block _ ih =>
      obtain ⟨_, costed⟩ := ih
      exact ⟨_, .block costed⟩
  | binding initializer _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .binding childCost tailCost⟩
  | inferred initializer _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp initializer
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .inferred childCost tailCost⟩
  | discard expression _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp expression
      obtain ⟨_, tailCost⟩ := ih
      exact ⟨_, .discard childCost tailCost⟩
  | ifTrue condition _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifTrue childCost branchCost⟩
  | ifFalse condition _ ih =>
      obtain ⟨_, childCost⟩ := childCostIff.mp condition
      obtain ⟨_, branchCost⟩ := ih
      exact ⟨_, .ifFalse childCost branchCost⟩

theorem computationReturnTreeEvaluates_iff_exists_cost
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} :
    ComputationReturnTreeEvaluates ChildEval owner table environment initialStore body value finalStore ↔
      ∃ cost, ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
        initialStore body value finalStore cost :=
  ⟨cost_exists childCostIff, fun ⟨_, evaluation⟩ => erase_cost childCostIff evaluation⟩

theorem ComputationReturnTreeEvaluatesWithCost.deterministic
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    (childDeterministic : ∀ {table environment initialStore source left right leftStore rightStore leftCost rightCost},
      ChildCost table environment initialStore source left leftStore leftCost →
      ChildCost table environment initialStore source right rightStore rightCost →
      left = right ∧ leftStore = rightStore ∧ leftCost = rightCost)
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore : Core.Store} {body : Syntax.Block} {left right : Core.Value}
    {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (first : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body left leftStore leftCost)
    (second : ComputationReturnTreeEvaluatesWithCost ChildCost owner table environment
      initialStore body right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  induction first generalizing right rightStore rightCost with
  | bare => cases second; exact ⟨rfl, rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact childDeterministic child other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := childDeterministic initializer otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl, rfl⟩ := childDeterministic initializer otherInitializer
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic expression otherExpression
          obtain ⟨rfl, rfl, rfl⟩ := ih otherTail
          exact ⟨rfl, rfl, rfl⟩
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic condition otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩
      | ifFalse otherCondition _ => cases (childDeterministic condition otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (childDeterministic condition otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl, rfl⟩ := childDeterministic condition otherCondition
          obtain ⟨rfl, rfl, rfl⟩ := ih otherBranch
          exact ⟨rfl, rfl, rfl⟩

end Solcore.Frontend
