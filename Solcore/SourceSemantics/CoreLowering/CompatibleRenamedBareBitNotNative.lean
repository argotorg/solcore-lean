import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotNative
import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement
import Solcore.SourceSemantics.CoreLowering.LoopRenaming

/-! Exact syntax transport of the absent-RHS bare assignment. Its helper
closures are created in the actual environment; no existing captured closure
or stored value is replaced by a weakened evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

private theorem getter_rename (prepared : Prepared) (layout : Layout prepared) (ξ : Renaming) :
    (getter prepared .unit).rename ξ = getter prepared .unit := by
  simp [getter, layout.steps, normalizeRoot, layout.ordinary, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem setter_rename (prepared : Prepared) (layout : Layout prepared) (ξ : Renaming) :
    (setter prepared .unit).rename ξ = setter prepared .unit := by
  simp [setter, layout.steps, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem modified_rename (type : Ty) (operator : Option BinaryOp) (invalid : Word) (ξ : Renaming) :
    (modified type operator true (.var 1) (.var 0) invalid).rename ξ.lift.lift =
      modified type operator true (.var 1) (.var 0) invalid := by
  simp [modified, LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- Only the free lexical reference and continuation move. The Unit RHS stays
an administrative slot and is never represented as a source expression. -/
theorem execute_rename {prepared : Prepared} (layout : Layout prepared) (index : Nat)
    (next : Expr) (output : Ty) (operator : Option BinaryOp) (invalid : Word) (ξ : Renaming) :
    (execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
      next output operator true invalid).rename ξ =
    execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
      (next.rename ξ) output operator true invalid := by
  simp [execute, SourceCoreCalls.packArguments, LanguageResult.bind, LanguageResult.success,
    shift, List.range, List.range.loop, List.foldl, Expr.rename, Expr.weakenAt,
    getter_rename _ layout, setter_rename _ layout, modified_rename, Renaming.lift]

def writtenContext (prepared : Prepared) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.rootType :: .unit ::
    OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: context
end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
