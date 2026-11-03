import Solcore.Core.LocalLoop
import Solcore.Core.OptionalCell
import Solcore.Core.LanguageResult

/-! The code a generalized declaration emits. Its scope copies wrap the bundle
initializer and the marked descriptor allocation; the continuation runs over
the original scope. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode
open Core

/-- The bundle initializer bound below the descriptor allocation, inside the
copies. -/
def snapshotInner (payload : Ty) (initializer allocation : Expr) : Expr :=
  LanguageResult.bind (OptionalCell.referenceType payload) initializer (LanguageResult.success allocation)

/-- The copies with the bundle and its allocation, then the continuation over
the original scope. -/
def snapshotSequence (type : Ty) (copied body : Expr) : Expr :=
  LanguageResult.bind (LocalLoop.controlType type) copied body

end Solcore.SourceSemantics.CoreLowering.CellAwareGeneralizedSnapshotCode
