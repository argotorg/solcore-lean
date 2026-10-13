import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {program : Program}
  (receipt : Receipt policy body fuel compilation values source scope id callee ids instantiation reasonAt lowered)

theorem source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
    (ready : Ready receipt catalog) {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty}
    (shaped : SelectedCompilationSourceSignatureFacts.Shape ready.header)
    (signatures : context.signatures = program.signatures)
    (application : DeclarationApplicationValid context instantiation types
      receipt.node.type instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      receipt.node.type = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := shaped _
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectSourceTypes
