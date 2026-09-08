import Solcore.Frontend.TypedLetReturnTreeEvaluatorCorrespondence
import Solcore.Frontend.TypedLetReturnTreeEvaluationProperties

/-! Exact store-free outputs characterize raw recursive paths, not whole-body
acceptance. General store correspondence explicitly retains the final store. -/
set_option autoImplicit false
namespace Solcore.Frontend

theorem evaluateTypedLetReturnTreeWithCost?_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} {cost : Nat} (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) ↔
      TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost :=
  ⟨fun accepted => evaluateTypedLetReturnTreeWithCost?_sound accepted store,
    evaluateTypedLetReturnTreeWithCost?_complete⟩

theorem typedLetReturnTreeEvaluatesWithCost_iff_evaluate
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {initialStore finalStore : Core.Store} {body : Syntax.Block} {value : Core.Value} {cost : Nat} :
    TypedLetReturnTreeEvaluatesWithCost owner table environment initialStore body value finalStore cost ↔
      finalStore = initialStore ∧
        evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost) := by
  constructor
  · intro evaluation
    exact ⟨evaluation.store_eq, evaluateTypedLetReturnTreeWithCost?_complete evaluation⟩
  · rintro ⟨rfl, accepted⟩
    exact evaluateTypedLetReturnTreeWithCost?_sound accepted _

theorem evaluateTypedLetReturnTreeWithCost?_eq_none_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} (store : Core.Store) :
    evaluateTypedLetReturnTreeWithCost? owner table environment body = none ↔
      ¬ ∃ value cost, TypedLetReturnTreeEvaluatesWithCost owner table environment store body value store cost := by
  constructor
  · intro absent ⟨value, cost, evaluation⟩
    have accepted := evaluateTypedLetReturnTreeWithCost?_complete evaluation
    rw [absent] at accepted
    cases accepted
  · intro absent
    cases result : evaluateTypedLetReturnTreeWithCost? owner table environment body with
    | none => rfl
    | some pair =>
        exact False.elim (absent ⟨pair.1, pair.2, evaluateTypedLetReturnTreeWithCost?_sound result store⟩)

theorem evaluateTypedLetReturnTreeWithCost?_exists_cost_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} (store : Core.Store) :
    (∃ cost, evaluateTypedLetReturnTreeWithCost? owner table environment body = some (value, cost)) ↔
      TypedLetReturnTreeEvaluates owner table environment store body value store := by
  constructor
  · rintro ⟨cost, accepted⟩
    exact (evaluateTypedLetReturnTreeWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, costed⟩ := evaluation.exists_cost
    exact ⟨cost, evaluateTypedLetReturnTreeWithCost?_complete costed⟩

theorem evaluateTypedLetReturnTreeWithCost?_value_iff
    {owner : Resolved.DeclarationId} {table : LocalNameTable} {environment : Resolved.Environment}
    {body : Syntax.Block} {value : Core.Value} (store : Core.Store) :
    (evaluateTypedLetReturnTreeWithCost? owner table environment body).map Prod.fst = some value ↔
      TypedLetReturnTreeEvaluates owner table environment store body value store := by
  constructor
  · intro projected
    obtain ⟨⟨actual, cost⟩, accepted, same⟩ := Option.map_eq_some_iff.mp projected
    cases same
    exact (evaluateTypedLetReturnTreeWithCost?_sound accepted store).erase
  · intro evaluation
    obtain ⟨cost, accepted⟩ := (evaluateTypedLetReturnTreeWithCost?_exists_cost_iff store).mpr evaluation
    simp only [accepted, Option.map_some]

end Solcore.Frontend
