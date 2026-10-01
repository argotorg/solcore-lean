import Solcore.Frontend.SourceCoreCallableIndexedDispatch
import Solcore.Core.Derived

/-! Syntactic renaming of the finite indexed protocol. Renaming moves the
emitted scalar selectors together with their lexical slots. No claim about
exact equality of closure values or stores across an insertion is made. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
open Core Frontend.SourceCoreCallableIndexedFrames Frontend.SourceCoreCallableIndexedDispatch
abbrev NativeFrame := Frontend.SourceCoreCallableIndexedFrames.Frame

@[simp] theorem literal (layout : Layout) (frame : NativeFrame) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.literal layout frame).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.literal layout frame := by
  cases frame <;> rfl

@[simp] theorem plainDispatch (table : Table) (layout : Layout) (origin : Word) (lexical : Expr)
    (rows : List LambdaEdge) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.plainDispatch table layout origin lexical rows).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.plainDispatch table layout origin (lexical.rename ξ) rows := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    simp only [Frontend.SourceCoreCallableIndexedDispatch.plainDispatch]
    split <;> simp only [Expr.rename, literal, ih]

@[simp] theorem viewDispatch (table : Table) (layout : Layout) (origin : Word) (id caller lexical : Expr)
    (rows : List ViewEdge) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.viewDispatch table layout origin id caller lexical rows).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.viewDispatch table layout origin (id.rename ξ)
        (caller.rename ξ) (lexical.rename ξ) rows := by
  induction rows with
  | nil => rfl
  | cons edge rest ih =>
    simp only [Frontend.SourceCoreCallableIndexedDispatch.viewDispatch]
    split <;> simp only [Expr.rename, literal, ih]

@[simp] theorem lambdaFrame (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr)
    (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin lexical current).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin
        (lexical.rename ξ) (current.rename ξ) := by
  simp [Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame, Expr.rename, Expr.renameList,
    Frontend.SourceCoreCallableIndexedFrames.invalid, Renaming.lift]

@[simp] theorem lambdaFrame_weaken (table : Table) (layout : Layout) (origin : Word) (lexical current : Expr)
    (cutoff : Nat) :
    (Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin lexical current).weakenAt cutoff =
      Frontend.SourceCoreCallableIndexedDispatch.lambdaFrame table layout origin
        (lexical.weakenAt cutoff) (current.weakenAt cutoff) := by
  simpa only [Expr.rename_insertion] using lambdaFrame table layout origin lexical current (Renaming.insertion cutoff)

@[simp] theorem readView (layout : Layout) (id target : Word) (current : Expr) (ξ : Renaming) :
    (Frontend.SourceCoreCallableIndexedDispatch.readView layout id target current).rename ξ =
      Frontend.SourceCoreCallableIndexedDispatch.readView layout id target (current.rename ξ) := by
  simp [Frontend.SourceCoreCallableIndexedDispatch.readView, Expr.rename, Expr.renameList,
    Frontend.SourceCoreCallableIndexedFrames.invalid, Frontend.SourceCoreCallableIndexedFrames.view, Renaming.lift]

@[simp] theorem readView_weaken (layout : Layout) (id target : Word) (current : Expr) (cutoff : Nat) :
    (Frontend.SourceCoreCallableIndexedDispatch.readView layout id target current).weakenAt cutoff =
      Frontend.SourceCoreCallableIndexedDispatch.readView layout id target (current.weakenAt cutoff) := by
  simpa only [Expr.rename_insertion] using readView layout id target current (Renaming.insertion cutoff)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedRenaming
