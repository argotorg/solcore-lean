import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedStageOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning

/-! The existing nested-body model supplies function-leaf provenance from its
actual cached caller and same-Code static body. Its environments, heaps and
body meaning continue to use that identical model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedLambdaRuntimeValues
open CallableIndexedLambdaNestedRuntimeCertificates RecursiveNamedCatalog

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
  {locations : Locations (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (program := program)}

/-- The stored caller is an actual cached header. The body supplies full source
identity and occurrence uniqueness independently of captured history. -/
theorem support_provenance {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    (body : CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults code) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source := by
  obtain ⟨caller, rank, body⟩ := body
  let receipt := body.receipt
  refine ⟨?_, receipt.body.unique⟩
  rw [receipt.compilation, receipt.active, receipt.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)

/-- A particular function leaf receives the source receipt established by its
own static support. No heap or function-model conversion is performed. -/
theorem origin_of_represents
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {carrier : Value} {type : Ty}
    (related : (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile).Represents registry
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table source carrier := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  cases related with
  | retained previous =>
    exact CallableIndexedStageOrigins.retained_origin (values := .initial compiled.compatible.checked) compiled.indexed prepared.accepted previous
  | lambda captured code history body supported typed =>
    have original := support_provenance (headers := headers) (registry := registry) (faults := faults) compiled body
    have provenance : CallableIndexedStageOrigins.provenanceCondition (values := .initial compiled.compatible.checked)
        compiled.indexed compiled.sourceProgram
        (CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults)
        (CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations)
        captured code history body := ⟨supported, original⟩
    exact CallableIndexedStageOrigins.origin_of_represents (values := .initial compiled.compatible.checked) compiled.indexed
      (support := CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults) (prior := CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations)
      prepared.accepted (RepresentsWith.lambda (values := .initial compiled.compatible.checked)
        (prepared := compiled.indexed) captured code history body provenance typed)

/-- Function origins are observations of the same nested model used by body
meaning. Actual sidecar and callsite equalities select its stage table. -/
theorem function_origins
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = compiled.indexed.base.plan)
    (sameTable : site.table = compiled.indexed.ancestry.graph.inputs.callable.table) :
    CompatibleAmbientStageOrigins.FunctionOrigins
      (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile) registry sidecar site := by
  intro mapping world sourceType source carrier type related
  rw [samePlan, sameTable]
  exact origin_of_represents compiled profile related

private theorem callsite_table {table : SourceCoreStageCodebook.Table}
    {owner : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {reasonAt : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table owner call reasonAt = .ok site) :
    site.table = table := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

/-- All guard rows and function-leaf origins come from this actual compilation
and its existing nested model. The whole source and native heap stay unchanged. -/
theorem actual_compiled_coverage
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {context : SourceCoreFunctions.Context} {node : ExpressionNode} {callee : ExpressionId}
    {arguments : List ExpressionId} {metadata : IndirectCallResolution}
    {site : SourceCoreCallableContracts.Callsite} {sidecar : SourceCoreStageContracts.Sidecar}
    (issued : SourceCoreCallableContracts.prepareCallsite compiled.indexed.ancestry.graph.inputs.callable.table context.owner node.id
      compiled.indexed.ancestry.graph.inputs.callable.diagnostics.reasonAt = .ok site)
    (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan context.owner = .ok sidecar)
    (contains : ContainsExpression sidecar.source node.id node)
    (form : node.form = .call callee arguments (.indirect metadata))
    (sourceType : TypeSystem.Ty) (type : Ty) :
    CallStageBoundary.CoversFor
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  intro mapping world source carrier contract represented bound
  exact CompatibleAmbientStageOrigins.actual_coverage prepared issued caller contains form
    (function_origins compiled profile (CallContractCertificates.sidecar_of_accepted caller).1
      (callsite_table issued)) sourceType type represented bound

/-- Callers recover the original captures, static body and capture condition.
The additional source attribution is derived from that exact stored body. -/
theorem closure_receipt
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty}
    (related : (CallableIndexedLambdaNestedRuntimeCertificates.model (values := .initial compiled.compatible.checked) headers locations registry faults profile).Represents registry
      mapping world sourceType (.closure function) native type) :
    ∃ scope actual, ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : CallableIndexedLambdaNestedRuntimeCertificates.Support (values := .initial compiled.compatible.checked) headers registry faults code),
      CallableIndexedLambdaNestedRuntimeCertificates.Condition (values := .initial compiled.compatible.checked) (registry := registry) (faults := faults) headers locations captured code history body ∧
      LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
        code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source ∧
      sourceType = FunctionValues.sourceType function ∧
      native = value code captured.embedding history.native actual ∧
      type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨scope, actual, captured, code, history, body, condition, sourceEq, nativeEq, typeEq⟩ :=
    RepresentsWith.closure_inv (values := .initial compiled.compatible.checked) compiled.indexed related
  obtain ⟨source, unique⟩ := support_provenance compiled body
  exact ⟨scope, actual, captured, code, history, body, condition, source, unique, sourceEq, nativeEq, typeEq⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
