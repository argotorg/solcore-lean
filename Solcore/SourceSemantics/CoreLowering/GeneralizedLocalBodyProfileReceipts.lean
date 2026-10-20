import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate

/-! The profile stored by the actual initializer determines its materialized
body and ordinary expression certificate. No terminal execution law is supplied. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)

theorem view_source : material.code.view = function.source := material.view.trans material.source.symm

theorem terminal : Terminal material.code.view material.bodyProfile.expression function.body := by
  have found := material.code.found
  rw [material.codeId, material.view] at found
  have same := Option.some.inj (material.bodyProfile.found.symm.trans found)
  have form := material.code.form.trans material.code.sourceForm
  have bodies := (ExpressionForm.lambda.inj (material.bodyProfile.form.symm.trans
    ((congrArg ExpressionNode.form same).trans form))).2.2
  rw [material.view, ← bodies]
  exact material.bodyProfile.terminal

def expression_site : GeneralizedLocalBodyExpressionCertificate.Site material.inputs material.code.view
    material.bodyProfile.expression := by
  rw [material.view]
  exact material.bodyProfile.expressionSite

theorem expression_profile : GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner
    material.code.view material.bodyProfile.expression := by
  rw [material.view]
  exact material.bodyProfile.expressionTree

theorem receipt : Nonempty (Receipt (GeneralizedLocalBodyCompiler.policy material)
    material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    material.bodyProfile.expression function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body) :=
  GeneralizedLocalBodyCompiler.terminal_receipt material (terminal material)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
