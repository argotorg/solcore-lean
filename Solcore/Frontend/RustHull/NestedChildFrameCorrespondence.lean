import Solcore.Frontend.RustHull.NestedChildFrameInvokeCorrespondence
import Solcore.Frontend.RustHull.NestedChildCatalogRunCorrespondence

/-! Finite source call trees determine actual compiled child execution. The
induction counts source child frames independently of Core evaluation fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
open NestedChildCatalogExecutionCorrespondence

theorem frame_execution (sourceCatalog : ChildFrameSemantics.Catalog)
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (height : Nat) : FrameExecution sourceCatalog catalog anchors (ChildFrameSemantics.effectsAt sourceCatalog height) := by
  induction height with
  | zero =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references parent ambient
      dsimp only
      intro caller request shared response final impossible
      cases impossible
  | succ height induction =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures images cells creator layout initial capture
        inventory references parent ambient
      exact captured_child_runs_preserves connection induction compiled closures capture inventory references parent ambient

end Solcore.Frontend.RustHull.NestedChildFrameCorrespondence
