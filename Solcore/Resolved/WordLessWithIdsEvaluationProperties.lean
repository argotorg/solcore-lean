import Solcore.Resolved.WordLessWithIds
import Solcore.Resolved.ScopeExtensionReflectionProperties

/-! Ordered evaluation for explicit comparison temporaries. Freshness prevents
capture of existing right references; original right scoping is additionally
needed for reflection, since insertion can otherwise enable a missing name. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Both original operands evaluate exactly once in source order. No type,
allocation or whole-expression scoping premise is needed in this direction. -/
theorem Evaluates.wordLtWithIds
    {environment : Environment} {initialStore middleStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {leftWord rightWord : Core.Word}
    (leftEvaluation : Evaluates environment initialStore left (.word leftWord) middleStore)
    (rightEvaluation : Evaluates environment middleStore right (.word rightWord) finalStore)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    Evaluates environment initialStore (Expr.wordLtWithIds leftId rightId left right)
      (.bool (decide (leftWord < rightWord))) finalStore :=
  .letE leftEvaluation (.letE (rightEvaluation.weaken_fresh leftFresh)
    (.binary (.var .head) (.var (.tail different .head)) rfl))

/-- Reflection recovers the original right evaluation, not an evaluation enabled
by its new surrounding temporary. The second temporary may shadow an outer ID. -/
theorem Evaluates.wordLtWithIds_inv
    {environment : Environment} {initialStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore
      (Expr.wordLtWithIds leftId rightId left right) value finalStore)
    (rightScoped : WellScoped (LocalScope.ids environment) right)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    ∃ leftWord rightWord middleStore,
      Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  cases evaluation with
  | @letE _ _ _ _ _ _ _ boundLeft _ leftEvaluation bodyEvaluation =>
      cases bodyEvaluation with
      | @letE _ _ _ _ _ _ _ boundRight _ rightEvaluation comparison =>
          cases comparison with
          | binary rightReference leftReference applied =>
              cases rightReference with
              | var foundRight =>
                  cases foundRight.value_unique .head
                  cases leftReference with
                  | var foundLeft =>
                      cases foundLeft.value_unique (.tail different .head)
                      cases boundRight <;> cases boundLeft <;>
                        simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          rightScoped.evaluates_weaken_fresh_iff leftFresh |>.mp rightEvaluation, rfl⟩

/-- Exact two-child semantics under the necessary original-right scope and
hygiene premises. No executable-run assumption occurs on either side. -/
theorem wordLtWithIds_evaluates_iff
    {environment : Environment} {initialStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {value : Core.Value}
    (rightScoped : WellScoped (LocalScope.ids environment) right)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    Evaluates environment initialStore (Expr.wordLtWithIds leftId rightId left right)
      value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates environment initialStore left (.word leftWord) middleStore ∧
        Evaluates environment middleStore right (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord)) := by
  constructor
  · intro evaluation
    exact evaluation.wordLtWithIds_inv rightScoped leftFresh different
  · rintro ⟨leftWord, rightWord, middleStore, leftEvaluation, rightEvaluation, rfl⟩
    exact leftEvaluation.wordLtWithIds rightEvaluation leftFresh different

end Solcore.Resolved
