import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadCertificate
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyExpressionCertificate

/-! The actual materialization identifies the original complete lambda body.
Its finite scanner receipt retains ordinary leaves and changing lexical scopes;
no caller supplies an execution law for that body. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)

theorem view_source : material.code.view = function.source := material.view.trans material.source.symm

theorem lambda_fields : material.bodyProfile.parameters = function.parameters ∧
    material.bodyProfile.result = function.resultType ∧ material.bodyProfile.body = function.body := by
  have found := material.code.found
  rw [material.codeId, material.view] at found
  have same := Option.some.inj (material.bodyProfile.found.symm.trans found)
  have form := material.code.form.trans material.code.sourceForm
  exact ExpressionForm.lambda.inj (material.bodyProfile.form.symm.trans
    ((congrArg ExpressionNode.form same).trans form))

theorem scan : ScopedSourceBodyAdmission.Scan material.code.view
    (GeneralizedLocalOrdinaryExpressionProfile.Tree material.inputs.locals material.inputs.current.owner material.code.view)
    function.resultType true function.body := by
  obtain ⟨_,result,body⟩ := lambda_fields material
  rw [material.view]
  simpa only [result,body] using material.bodyProfile.scan

theorem lexical : CellAwareOrdinaryBodySyntax.lexicalOnly material.code.view
    (material.code.view.nodes.length + 1) function.body = true := by
  obtain ⟨_,_,body⟩ := lambda_fields material
  rw [material.view]
  simpa only [body] using material.bodyProfile.lexical

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
