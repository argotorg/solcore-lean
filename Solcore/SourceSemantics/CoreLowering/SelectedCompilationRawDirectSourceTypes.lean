import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceSignatureFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectSourceTypes
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Ready)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {compilation : SourceCoreFunctions.Context} {child : SourceCoreEvidence.Child} {budget : Nat}
  {source : TypedSource} {scope : SourceCoreBasic.Scope} {id callee : ExpressionId}
  {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {callables : SourceCoreFunctions.CallablePolicy}
  {node : ExpressionNode} {output : SourceCoreBasic.LoweredExpr}
  (actual : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    child budget source scope id callee ids instantiation reasonAt callables node output)

theorem source_types
    {catalog : List (CallableIndexedOwnedFunctionValues.Header compiled
      (Program.ofChecked compiled.sourceProgram))}
    (ready : Ready actual catalog) {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (shaped : SelectedCompilationSourceSignatureFacts.Shape ready.header)
    (signatures : context.signatures = compiled.sourceProgram.signatures)
    (application : DeclarationApplicationValid context instantiation types node.rawType instantiation.predicates) :
    types = ready.header.bindings.map (fun binding => binding.1.scheme.body) ∧
      node.rawType = ready.header.function.resultType := by
  cases application with
  | intro member admissible declaration parameters result functionType predicates =>
    have shape := shaped _
      (signatures ▸ member) (by rw [← ready.metadata]; exact declaration)
    rw [← ready.metadata] at shape
    exact ⟨parameters.symm.trans shape.1, result.symm.trans shape.2⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawDirectSourceTypes
