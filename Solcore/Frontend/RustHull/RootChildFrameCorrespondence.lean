import Solcore.Frontend.RustHull.RootChildFrameInvokeCorrespondence
import Solcore.Frontend.RustHull.RootChildCatalogRunCorrespondence

/-! Finite source call trees determine actual compiled child execution. The
induction counts source child frames independently of Core evaluation fuel. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RootChildFrameCorrespondence
open RootChildCatalogExecutionCorrespondence

theorem frame_execution (rootSource : ChildFrameSemantics.Code) (sourceCatalog : ChildFrameSemantics.Catalog)
    {initCatalog : ChildFrameSemantics.InitCatalog}
    (catalog : List AccountRuntime.CodeDefinition) (anchors : List CatalogWorldCorrespondence.Anchor)
    (height : Nat) : FrameExecution rootSource sourceCatalog catalog anchors (ChildFrameModeSemantics.effectsAt sourceCatalog initCatalog height) := by
  induction height with
  | zero =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures rootCaptured images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      dsimp only
      intro caller request shared response final impossible
      cases impossible
  | succ height induction =>
      apply frame_execution_of_callbacks
      intro fuel others compiled connection captured values closure closures rootCaptured images cells creator layout initial capture
        inventory references create createAt mode parent ambient
      exact captured_child_runs_preserves connection induction compiled closures rootCaptured capture inventory references create createAt
        mode parent ambient

end Solcore.Frontend.RustHull.RootChildFrameCorrespondence
