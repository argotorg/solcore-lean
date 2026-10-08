import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues

/-! Genuine original ranked support already contains a complete same-Code
static body. This finite projection keeps its Header, Source, certificate
family and compiler receipts; the original full history seed remains the same.
No new static rank or body execution proof is constructed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedRankedOrdinarySupportReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  (body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code)

/-- The existing receipt supplies every unrestricted support field verbatim.
Its independent static rank remains inside the original certificate family. -/
def support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults := by
  let actual := CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2
  exact ⟨body.1, _, _, actual.source, actual.compilation, actual.active, actual.body⟩

/-- The selected genuine Header is unchanged. -/
theorem caller : (support body).caller = body.1 := rfl

include body in
/-- The original static receipt authenticates the same compiler prefix. -/
theorem native_prefix : administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) (support body).caller :=
  (CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2).administrative

/-- The complete original ClosureFrame is retained, including raw Source. -/
theorem frame : (support body).body.frame =
    (CallableIndexedLambdaNestedRuntimeCertificates.BodyAt.receipt body.2.2).body.frame := rfl

/-- The actual original Source origin identifies this same complete seed. -/
theorem source_origin (history : History code)
    (origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code history body) :
    CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin (support body) history :=
  ⟨origin.historyMetadata⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedRankedOrdinarySupportReceipts
