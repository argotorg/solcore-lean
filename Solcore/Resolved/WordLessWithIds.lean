import Solcore.Resolved.Renaming
import Solcore.Resolved.Scope
import Solcore.Core.Derived

/-! An explicit-identity builder for ordered Word less-than. The two operands
are evaluated once, left before right; only their retained values are swapped.
No identity is allocated and no source resolver or expression constructor is
extended. Freshness concerns the outer scope, not inner source binders. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Retain both operand values before comparing the right Word to the left.
The caller supplies both identities; this builder does not enforce hygiene. -/
def Expr.wordLtWithIds (leftId rightId : LocalId) (left right : Expr) : Expr :=
  .letE leftId left
    (.letE rightId right (.binary .wordGt (.var rightId) (.var leftId)))

/-- Structural renaming commutes even for noninjective identity maps. This
identity alone does not assert that such a map preserves hygiene or meaning. -/
@[simp] theorem Expr.renameIds_wordLtWithIds (leftId rightId : LocalId)
    (left right : Expr) (mapping : LocalId → LocalId) :
    (Expr.wordLtWithIds leftId rightId left right).renameIds mapping =
      Expr.wordLtWithIds (mapping leftId) (mapping rightId)
        (left.renameIds mapping) (right.renameIds mapping) :=
  rfl

/-- Exact lowering includes weakening the right operand under the retained
left value. The second identity may already occur in the original scope. -/
theorem Lowers.wordLtWithIds {scope : List LocalId} {leftId rightId : LocalId}
    {left right : Expr} {leftCore rightCore : Core.Expr}
    (lowerLeft : Lowers scope left leftCore)
    (lowerRight : Lowers scope right rightCore)
    (leftFresh : leftId ∉ scope) (different : rightId ≠ leftId) :
    Lowers scope (Expr.wordLtWithIds leftId rightId left right)
      (Core.Expr.wordLt leftCore rightCore) := by
  rw [Core.Expr.wordLt_expansion]
  exact .letE lowerLeft (.letE (lowerRight.weaken_fresh leftFresh)
    (.binary (.var .head) (.var (.tail different .head))))

/-- Both original operands are checked as Words before introducing the
temporary bindings. No freshness assumption is imposed on inner binders. -/
theorem HasType.wordLtWithIds {context : Context} {leftId rightId : LocalId}
    {left right : Expr}
    (leftTyping : HasType context left .word)
    (rightTyping : HasType context right .word)
    (leftFresh : leftId ∉ LocalScope.ids context) (different : rightId ≠ leftId) :
    HasType context (Expr.wordLtWithIds leftId rightId left right) .bool :=
  .letE leftTyping (.letE (rightTyping.weaken_fresh leftFresh .word)
    (.binary (.var .head) (.var (.tail different .head))))

theorem Expr.lower?_wordLtWithIds {scope : List LocalId} {leftId rightId : LocalId}
    {left right : Expr} {leftCore rightCore : Core.Expr}
    (lowerLeft : left.lower? scope = some leftCore)
    (lowerRight : right.lower? scope = some rightCore)
    (leftFresh : leftId ∉ scope) (different : rightId ≠ leftId) :
    (Expr.wordLtWithIds leftId rightId left right).lower? scope =
      some (Core.Expr.wordLt leftCore rightCore) :=
  ((Expr.lower?_sound lowerLeft).wordLtWithIds
    (Expr.lower?_sound lowerRight) leftFresh different).complete

theorem infer_wordLtWithIds {context : Context} {leftId rightId : LocalId}
    {left right : Expr}
    (leftInferred : infer? context left = some .word)
    (rightInferred : infer? context right = some .word)
    (leftFresh : leftId ∉ LocalScope.ids context) (different : rightId ≠ leftId) :
    infer? context (Expr.wordLtWithIds leftId rightId left right) = some .bool :=
  infer_complete ((infer_sound leftInferred).wordLtWithIds
    (infer_sound rightInferred) leftFresh different)

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.WordLessWithIdsEvaluationProperties`
-/

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
