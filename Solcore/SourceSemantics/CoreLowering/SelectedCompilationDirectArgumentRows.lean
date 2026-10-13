import Solcore.SourceSemantics.CoreLowering.SelectedCompilationNamedAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallAuthority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedArgumentRows

/-! Direct declaration calls retain the independently typed Source argument
row. Every raw replacement is closed; original Source admissibility recovers
its validity. Actual evidence production supplies the full callable dictionary;
authentic compiler bundles align native arguments only after the Source row
supplies physical arity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
  {invocation : Staging.Recursive.Scope} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation values invocation.source scope id callee ids
    instantiation reasonAt lowered)
  (port : Port receipt headers)
  {context : SourceSemantics.Context}
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)

section Successful
variable {stages : Staging.Recursive.Registry} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {sourceTypes : List TypeSystem.Ty}
  {arguments : List Dynamic.Value} {payloads : List Value}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {mapping : LocationMap} {world : StoreTyping}

include receipt port in
theorem at_successful_arguments
    (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
    (heapTyped : Dynamic.HeapWellTyped context after)
    (argumentsTyped : Dynamic.ValuesHaveTypes context after arguments
      (port.header.bindings.map (fun binding => binding.1.scheme.body)))
    (represented : DataExpressionSequence.Values model mapping world
      (port.header.bindings.map (fun binding => binding.1.scheme.body))
      (receipt.codes.map (·.type)) arguments payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world port.header.bindings arguments payloads ∧
      Dynamic.HeapWellTyped port.header.function.context after ∧
      Dynamic.ValuesHaveTypes port.header.function.context after arguments port.header.types ∧
      Dynamic.TypeContextSupports port.header.context context := by
  have binderCount : arguments.length = port.header.bindings.length := by
    simpa only [List.length_map] using
      (CallableIndexedOwnedStoredArgumentAlignment.source_length represented).symm
  have nativePacked : SourceCoreCompatibleCatalog.packTypes (receipt.codes.map (·.type)) =
      SourceCoreCompatibleCatalog.packTypes (port.header.bindings.map Prod.snd) :=
    (CompatibleExpressionConstructorNativeTyping.packed_type receipt.codes).symm.trans
      (receipt.parameter.symm.trans
        ((congrArg SourceCoreCalls.Signature.parameterType port.signature).symm.trans port.header.parameterType))
  have representedRows := CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles
    port.header.bindings represented binderCount rfl nativePacked
  obtain ⟨bodyHeap, bodyArguments, supports⟩ :=
    SelectedCompilationNamedAdmission.arguments certified runtime heapTyped argumentsTyped
  exact ⟨representedRows, bodyHeap, bodyArguments, supports⟩
end Successful
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationDirectArgumentRows
