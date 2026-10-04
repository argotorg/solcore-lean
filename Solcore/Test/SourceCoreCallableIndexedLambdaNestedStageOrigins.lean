import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedStageOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaRuntimeEntry

/-! The actual nested model carries both body receipts and stage origins.
These consumers keep the original model and its invocation conditions. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedLambdaNestedStageOrigins
open Solcore
open Core Frontend SourceSemantics
open SourceInference SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaNestedRuntimeCertificates CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedCatalog

variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {program : SourceSemantics.Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
  {locations : Locations (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (program := program)}
local notation "F" => CallableIndexedLambdaNestedRuntimeCertificates.model
  (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) headers locations registry faults

section Actual

theorem header_source
    (header : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      header.named.signature.key [] header.function.source ∧ NodeOccurrencesUnique header.function.source :=
  CallableIndexedActualNamedSourceReceipts.header_source compiled header

/-- Recapture uses the actual source environment, including its unused tail. -/
theorem recaptured_source
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {rank : Nat} {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank source context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      (actualCode head environment).compilation.owner (actualCode head environment).active
      (formed head environment).source ∧ NodeOccurrencesUnique (formed head environment).source :=
  CallableIndexedLambdaNestedStageOrigins.support_provenance compiled (actualSupport head environment)

/-- The same formation evaluation and ValueRep also supply its stage origin. -/
theorem formed_origin
    {caller : Header compiled.indexed.ancestry (.initial compiled.compatible.checked) compiled.indexed.layouts.definitions program}
    {rank : Nat} {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = compiled.indexed.base.plan)
    (sameTable : site.table = compiled.indexed.ancestry.graph.inputs.callable.table)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    {canonical actual : Environment} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {ξ : Renaming}
    (entry : CallableIndexedLambdaNestedFormationEntries.Entry caller headers locations 0 1 scope mapping world heap store canonical)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    ∃ value,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head environment)) heap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) store ∧
      ValueRep compiled.compatible.checked registry (F profile) mapping world head.code.sourceNode.type
        (.closure (formed head environment)) value lowered.type ∧
      CallableLedger.OriginRep sidecar.plan site.table (.closure (formed head environment)) value := by
  obtain ⟨value, sourceValue, nativeValue, represented⟩ :=
    formation head profile complete globals slots entry related agrees typed stored
  exact ⟨value, sourceValue, nativeValue, represented,
    CompatibleAmbientStageOrigins.related_origin
      (CallableIndexedLambdaNestedStageOrigins.function_origins compiled profile samePlan sameTable)
      represented (.closure _)⟩

theorem actual_guards
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
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (F profile))
      (CallableLedger.frame sidecar) site node.id arguments sourceType type :=
  CallableIndexedLambdaNestedStageOrigins.actual_compiled_coverage compiled profile issued caller contains form sourceType type

end Actual

section Boundaries
/-- The original ordered capture condition remains available after attribution. -/
abbrev actual_closure_receipt := @CallableIndexedLambdaNestedStageOrigins.closure_receipt

/-- Invocation still consumes independently supplied catalog authority. -/
def caller_catalog
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment} {location : Location}
    {capturePrefix callerPrefix : Nat} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store}
    (captures : CallableIndexedLambdaCatalogEntries.CaptureGlobals
      (values := .initial compiled.compatible.checked) headers locations callerPrefix scope canonical location)
    (authority : Authority headers locations capturePrefix mapping world heap store) :
    Entry headers locations capturePrefix callerPrefix scope mapping world heap store canonical :=
  captures.catalog authority

/-- Retained builtin/data values do not acquire an arbitrary lambda history. -/
theorem scalar_not_callable (number : Int) : ¬ Staging.CallBoundary.UserCallable (.integer number) := by
  intro impossible
  cases impossible

/-- These existing body interfaces use F, its full heap and separate original
source/native grades. Stage coverage adds no body execution hypothesis. -/
abbrev same_model_body_preserves := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.preserves_sized
abbrev same_model_body_reflects := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.reflects_sized
abbrev same_model_entry := @CallableIndexedLambdaNestedRuntimeBodyMeaning.Body.entry_of_source
abbrev actual_lambda_permission := @CallableIndexedLambdaRuntimeEntry.reflects_original_nested_for
end Boundaries
end Tests.SourceCoreCallableIndexedLambdaNestedStageOrigins
