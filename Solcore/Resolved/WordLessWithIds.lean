import Solcore.Resolved.Renaming
import Solcore.Resolved.ScopeExtensionProperties
import Solcore.Core.DerivedComparisons

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
