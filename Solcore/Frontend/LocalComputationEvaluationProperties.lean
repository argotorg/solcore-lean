import Solcore.Frontend.LocalComputationEvaluation
import Solcore.Frontend.LocalFunctionApplicationEvaluationProperties

/-! The two original raw profiles keep their exact costs and outcomes.
Their root shapes are disjoint without any checker or typing premise. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem localComputationEvaluates_iff_exists_cost {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore finalStore : Core.Store}
    {source : Syntax.Expr} {value : Core.Value} :
    LocalComputationEvaluates table environment initialStore source value finalStore ↔
      ∃ cost, LocalComputationEvaluatesWithCost table environment
        initialStore source value finalStore cost := by
  constructor
  · intro evaluation
    cases evaluation with
    | pure child =>
        obtain ⟨cost, costed⟩ := child.exists_cost
        exact ⟨cost, .pure costed⟩
    | application child =>
        obtain ⟨cost, costed⟩ := child.exists_cost
        exact ⟨cost, .application costed⟩
  · rintro ⟨_, evaluation⟩
    cases evaluation with
    | pure child => exact .pure child.erase
    | application child => exact .application child.erase

theorem LocalComputationEvaluatesWithCost.deterministic {table : LocalNameTable}
    {environment : Resolved.Environment} {initialStore : Core.Store} {source : Syntax.Expr}
    {left right : Core.Value} {leftStore rightStore : Core.Store} {leftCost rightCost : Nat}
    (leftEvaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source left leftStore leftCost)
    (rightEvaluation : LocalComputationEvaluatesWithCost table environment
      initialStore source right rightStore rightCost) :
    left = right ∧ leftStore = rightStore ∧ leftCost = rightCost := by
  cases leftEvaluation with
  | pure child =>
      cases rightEvaluation with
      | pure other => exact child.deterministic other
      | application other => cases other; cases child
  | application child =>
      cases rightEvaluation with
      | pure other => cases child; cases other
      | application other => exact child.deterministic other

end Solcore.Frontend
