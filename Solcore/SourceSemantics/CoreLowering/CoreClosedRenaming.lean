import Solcore.Core.Renaming

/-! Static syntactic renaming of typed closed helper code. This concerns the
expression syntax only. It makes no claim that closures created in different
ambient environments are the same runtime value. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CoreProof
open Core

private theorem same_lift {context : Context} {left right : Renaming}
    (same : ∀ index, index < context.length → left index = right index) (type : Ty) :
    ∀ index, index < (type :: context).length → left.lift index = right.lift index := by
  intro index bound
  cases index with
  | zero => rfl
  | succ index => exact congrArg Nat.succ (same index (by simpa using bound))

/-- Renamings agreeing on every typed free slot produce identical syntax. -/
theorem typed_rename_agree {context : Context} {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType context expression type definitions) {left right : Renaming}
    (same : ∀ index, index < context.length → left index = right index) :
    expression.rename left = expression.rename right := by
  induction typed using HasType.rec
      (motive_2 := fun context _ _ branches _ _ => ∀ {left right : Renaming},
        (∀ index, index < context.length → left index = right index) →
        Expr.renameList branches left.lift = Expr.renameList branches right.lift)
      generalizing left right with
  | unit | bool | word | integer => rfl
  | var found => exact congrArg Expr.var (same _ (List.getElem?_eq_some_iff.mp found).1)
  | pair _ _ a b => simp only [Expr.rename, a same, b same]
  | first _ ih => exact congrArg Expr.first (ih same)
  | second _ ih => exact congrArg Expr.second (ih same)
  | lambda _ _ _ ih => simp only [Expr.rename, ih (same_lift same _)]
  | apply _ _ a b => simp only [Expr.rename, a same, b same]
  | inLeft _ _ ih => simp only [Expr.rename, ih same]
  | inRight _ _ ih => simp only [Expr.rename, ih same]
  | caseE _ _ _ a b c => simp only [Expr.rename, a same, b (same_lift same _), c (same_lift same _)]
  | newCell _ ih => simp only [Expr.rename, ih same]
  | loadCell _ ih => simp only [Expr.rename, ih same]
  | storeCell _ _ a b => simp only [Expr.rename, a same, b same]
  | construct _ _ ih => simp only [Expr.rename, ih same]
  | matchData _ _ _ _ a b => simp only [Expr.rename, a same, b same]
  | unary _ ih => simp only [Expr.rename, ih same]
  | binary _ _ a b => simp only [Expr.rename, a same, b same]
  | ternary _ _ _ a b c => simp only [Expr.rename, a same, b same, c same]
  | letE _ _ a b => simp only [Expr.rename, a same, b (same_lift same _)]
  | ifE _ _ _ a b c => simp only [Expr.rename, a same, b same, c same]
  | nil => rfl
  | cons _ _ a b =>
    rename_i left right same
    simp only [Expr.renameList, a (same_lift same _), b same]

theorem closed_rename {expression : Expr} {type : Ty} {definitions : DataEnvironment}
    (typed : HasType [] expression type definitions) (embedding : Renaming) : expression.rename embedding = expression := by
  have same := typed_rename_agree typed (left := embedding) (right := Renaming.id) (by intro index bound; simp at bound)
  simpa using same

end Solcore.SourceSemantics.CoreLowering.CoreProof
