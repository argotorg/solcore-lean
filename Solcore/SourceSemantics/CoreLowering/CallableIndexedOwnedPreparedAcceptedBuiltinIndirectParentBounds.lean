import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds

/-! An authentic builtin row and its two actual gates construct the argument
packet and application parts of the original accepted indirect parent. The
primitive producer runs once, preserves its argument store and Source heap,
and returns the original caller packet. Source and native grades stay separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinIndirectParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedPreparedContextualQualification (Facet)
open CallableIndexedOwnedPreparedPositiveFunctionOrigins
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedPreparedCatalogIndirectInvocationDispatcher
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix (Suffix)
universe u


section Primitive
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world before store)
  {arguments : List Dynamic.Value} {payloads : List Value}
  {function : Dynamic.BuiltinFunction} {invocation : Dynamic.EvidenceEnvironment} {native : Value}
  {sourceResult : TypeSystem.Ty} {resultCore : Ty}
  (receipt : Receipt (qualification := qualification) (headers := headers) (keys := keys)
    (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
    (certificates := certificates) (expressionSyntax := expressionSyntax)
    (mapping := mapping) (world := world) (before := before) (arguments := arguments) (payloads := payloads)
    functions (.builtin function) invocation native sourceResult resultCore)
  {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)

include receipt heaps observations in
private theorem preserves_builtin_receipt
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence invocation before (.builtin function) arguments outcome after) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues payloads] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions)
        (sourceResult := sourceResult) (resultCore := resultCore) initial outcome after value finalStore := by
  cases receipt with
  | builtin builtin represented invocation =>
    obtain ⟨value, evaluated, related, sameHeap⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.preserves functions observations builtin represented called
    subst after
    exact ⟨value, store, evaluated, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩

include receipt heaps observations in
private theorem reflects_builtin_receipt
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues payloads] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context callerEvidence invocation before (.builtin function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) (functions := functions)
        (sourceResult := sourceResult) (resultCore := resultCore) initial outcome after value finalStore := by
  cases receipt with
  | builtin builtin represented invocation =>
    obtain ⟨sourceSize, outcome, called, related, sameStore⟩ :=
      CallableIndexedOwnedPreparedBuiltinIndirectInvocationBounds.reflects functions observations builtin represented completed
    subst finalStore
    exact ⟨sourceSize, outcome, before, called, mapping, world, related, heaps,
      LocationMap.Extends.refl mapping, WorldExtends.refl world, AdministrativePreserved.refl mapping store,
      Dynamic.HeapMetadataExtend.refl before, initial, callerProtocol.refl initial⟩

private theorem result_at_raw_type {sourceResultType actualSourceResult : TypeSystem.Ty}
    {resultCore : Ty} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (same : SourceCoreRawMetadata.runtimeType sourceResultType = SourceCoreRawMetadata.runtimeType actualSourceResult)
    (related : FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld actualSourceResult resultCore faults outcome value) :
    FunctionCalls.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld sourceResultType resultCore faults outcome value := by
  cases related with
  | value payload => exact .value (.compatible same payload)
  | fault matched => exact .fault matched
end Primitive

private theorem before_arguments
    {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
    {callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution} {node : ExpressionNode}
    {function : Dynamic.BuiltinFunction} {native : Value} {row : SourceCoreStageCodebook.Decision}
    (receipt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar site
      callee ids metadata node function native row) (unknown : Word) :
    CallableContract.decision site.gates .beforeArguments unknown row.entry.id = none := by
  rw [site.decision_known .beforeArguments unknown row.entry.id row receipt.selected.found]
  have accepted : row.beforeArguments = .ok () := by
    simp only [SourceCoreStageCodebook.Decision.beforeArguments,
      SourceCoreStageCodebook.Decision.answer, receipt.unguarded]
  exact SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeArguments accepted

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {qualification : Facet compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {certificates : Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  {context : SourceSemantics.Context} {evidence invocation : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  {calleeNode : ExpressionNode} {function : Dynamic.BuiltinFunction} {calleeNative : Value}
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}

section Parent
variable {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {xi : Renaming}
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (parent : SourceParent compiler)
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree xi canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (firstAdmission : Admission bridge context first)
  (post : CallableIndexedOwnedStoredFunctionModelReceipts.ValuePost (registry := registry)
    (actual := actual) (ξ := xi) (calleeNode := calleeNode) (context := context)
    bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first (.builtin function) calleeHeap calleeNative store mapping world)
  (builtinAt : CallableIndexedOwnedContextualCalleeStageReceipts.BuiltinAt sidecar prepared.site
    callee ids metadata compiler.original function calleeNative row)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown row.entry.id = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee (.builtin function) calleeHeap)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) identities)

include certificates expressionSyntax invocation prepared actualFunctionType parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission post builtinAt secondGate calleeTrace observations
/-- The actual accepted builtin parent uses only its measured ordered expression
children. The primitive application has no body family premise. -/
theorem preserves (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile)) context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment
      calleeHeap ids (.builtin function) argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename xi) value finalStore ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler :=
    CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound calleeTyped represented builtinAt secondGate
  have firstGate := before_arguments builtinAt
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have callable : Dynamic.CallableValue (.builtin function) := by simp only [Dynamic.CallableValue]
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  have application : CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationPreserves
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler
      (context := context) (evidence := evidence) (environment := environment)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := .builtin function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := compiler.resultType)
      (sourceResultType := compiler.original.type) budget suffix := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
      rawArguments packing bundle argumentsSize callSize outcome after _argumentsTrace called _calledSuffix _within
    obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
      calleeTyped extension represented heaps rawArguments packing bundle
    obtain ⟨value, finalStore, evaluated, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, returnedRelated⟩ :=
      preserves_builtin_receipt (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) argumentState heaps receipt observations called
    exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result_at_raw_type (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) rawResult related,
      finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.preserves_with_application bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler prepared
    parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed first firstAdmission
    reached related maps worlds frame metadata callable nativeTyped heaps rfl rfl
    shape firstGate secondGate calleeTrace calleeEvaluation builtinAt.selected budget children suffix
    argumentsWithin callWithin application

include certificates expressionSyntax invocation prepared actualFunctionType parent tree unique parentTyped calleeFound wellFormed runtime covers
  environments locals agrees typed firstAdmission post builtinAt secondGate calleeTrace observations
/-- Reflection consumes the literal original native completion. Its own Source
suffix grade and returned caller witness come from the original parent inversion. -/
theorem reflects (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile)) context evidence source certificate faults size)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename xi) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        context evidence source environment before id outcome after ∧
      CallableIndexedOwnedStoredFunctionModelReceipts.ParentResultAt (registry := registry) (faults := faults)
        (context := context) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨calleeEvaluation, represented, heaps, maps, worlds, frame, metadata, reached, related, admission⟩ := post
  have calleeTyped := admission.at_value.1
  have packets : CallableIndexedOwnedPreparedCatalogIndirectApplicationBounds.ArgumentPackets
      (qualification := qualification) (headers := headers) (keys := keys)
      (bodyRegistry := bodyRegistry) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax)
      (context := context) (invocation := invocation) (canonical := canonical)
      (mapping := mapping) (world := world) (calleeHeap := calleeHeap) (store := store)
      (function := .builtin function) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := compiler.original.type) (resultCore := compiler.resultType)
      bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler :=
    CallableIndexedOwnedPreparedAcceptedBuiltinArgumentPackets.packets bridge compiler
      actualFunctionType parent tree unique parentTyped calleeFound calleeTyped represented builtinAt secondGate
  have firstGate := before_arguments builtinAt
    compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown
  obtain ⟨raw, shape⟩ := builtinAt.shape
  have callable : Dynamic.CallableValue (.builtin function) := by simp only [Dynamic.CallableValue]
  have nativeTyped := represented.runtime_hasType
  have signature := compiler.callableType
  rw [actualFunctionType] at signature
  rw [← signature] at nativeTyped
  have application : CallableIndexedOwnedPreparedIndirectValueParentBounds.ApplicationReflects
      (registry := registry) (faults := faults) bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler
      (context := context) (evidence := evidence) (invocation := invocation)
      (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := .builtin function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := compiler.resultType)
      (sourceResultType := compiler.original.type) budget := by
    intro middleMap middleWorld middle middleStore arguments payloads types parameter sourceResult packed
      argumentState admitted maps worlds frame metadata calleeTyped extension represented heaps
      rawArguments packing bundle size value finalStore completed _within
    obtain ⟨actualSourceResult, rawResult, receipt⟩ := packets argumentState admitted maps worlds frame metadata
      calleeTyped extension represented heaps rawArguments packing bundle
    obtain ⟨sourceSize, outcome, after, called, finalMap, finalWorld, related, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, returnedRelated⟩ :=
      reflects_builtin_receipt (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) argumentState heaps receipt observations completed
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, called, result_at_raw_type (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) rawResult related,
      finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, returned, returnedRelated⟩
  exact CallableIndexedOwnedPreparedIndirectValueParentBounds.reflects_with_application bridge (CallableIndexedOwnedPreparedPositiveFunctionOrigins.functions (compiled := compiled) qualification headers keys bodyRegistry faults profile) compiler prepared
    unique parentTyped first reached parent tree wellFormed runtime covers environments locals agrees typed firstAdmission
    related maps worlds frame metadata nativeTyped heaps rfl rfl callable
    shape firstGate secondGate calleeTrace calleeEvaluation builtinAt.selected budget children application completed within

end Parent
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedAcceptedBuiltinIndirectParentBounds
