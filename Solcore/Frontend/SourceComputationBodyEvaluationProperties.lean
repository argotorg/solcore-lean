import Solcore.Frontend.SourceComputationBodyEvaluation

/-! Body value/store determinism requires only the fixed owner's child law.
No cost, checking, typing, image or world assumption is used. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Value/store uniqueness follows solely from the fixed owner's child law;
no typing, child completeness, image or execution-cost premise is required. -/
theorem SourceComputationBodyEvaluates.deterministic
    {ChildEval : Resolved.DeclarationId → List (String × Resolved.LocalId) →
      List (Resolved.LocalId × RuntimeValue) → List RuntimeValue → Syntax.Expr →
      RuntimeValue → List RuntimeValue → Prop}
    {owner : Resolved.DeclarationId}
    (childDeterministic : ∀ {table environment initialStore source left right leftStore rightStore},
      ChildEval owner table environment initialStore source left leftStore →
      ChildEval owner table environment initialStore source right rightStore →
      left = right ∧ leftStore = rightStore)
    {table : List (String × Resolved.LocalId)} {environment : List (Resolved.LocalId × RuntimeValue)}
    {initialStore : List RuntimeValue} {body : Syntax.Block} {left right : RuntimeValue}
    {leftStore rightStore : List RuntimeValue}
    (first : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body left leftStore)
    (second : SourceComputationBodyEvaluates ChildEval owner table environment initialStore body right rightStore) :
    left = right ∧ leftStore = rightStore := by
  induction first generalizing right rightStore with
  | bare => cases second; exact ⟨rfl, rfl⟩
  | expression child =>
      cases second with
      | expression other => exact childDeterministic child other
  | block _ ih =>
      cases second with
      | block other => exact ih other
  | binding initializer _ ih =>
      cases second with
      | binding otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | inferred initializer _ ih =>
      cases second with
      | inferred otherInitializer otherTail =>
          obtain ⟨rfl, rfl⟩ := childDeterministic initializer otherInitializer
          exact ih otherTail
  | discard expression _ ih =>
      cases second with
      | discard otherExpression otherTail =>
          obtain ⟨_, rfl⟩ := childDeterministic expression otherExpression
          exact ih otherTail
  | ifTrue condition _ ih =>
      cases second with
      | ifTrue otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
      | ifFalse otherCondition _ => cases (childDeterministic condition otherCondition).1
  | ifFalse condition _ ih =>
      cases second with
      | ifTrue otherCondition _ => cases (childDeterministic condition otherCondition).1
      | ifFalse otherCondition otherBranch =>
          obtain ⟨_, rfl⟩ := childDeterministic condition otherCondition
          exact ih otherBranch
  | wordMatch scrutinee choice _ ih =>
      cases second with
      | wordMatch otherScrutinee otherChoice otherBranch =>
          obtain ⟨rfl, rfl⟩ := childDeterministic scrutinee otherScrutinee
          obtain ⟨rfl, rfl⟩ := choice.deterministic otherChoice
          exact ih otherBranch

end Solcore.Frontend
