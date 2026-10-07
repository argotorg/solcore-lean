import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads

/-! Selected indirect-call Source adapters retain the actual compiler receipt,
original parent node and prepared callsite. Caller protocols carry their same
actual pools separately from the selected closure capture protocol. Source suffix
construction uses original measured children; argument counts follow existing Source preservation
under real Source admission. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedIndirectExpressionHeads
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedExpressionHeads (argumentProtocol)

universe u

section LegacyBody
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
/-- Compatibility adds only the already authentic global-slot proof beside
one actual base entry and its same returned pool. -/
private theorem body_preserves_to_canonical
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
    {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size := by
  intro entry outcome after trace
  let baseEntry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) origin
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) :=
    { entry with initial := entry.initial.val }
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning baseEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, ⟨reached, entry.initial.property⟩, related⟩

/-- Native compatibility retains its independently obtained Source grade and
adds the same slot proof to the actual reached pool. -/
private theorem body_reflects_to_canonical
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
    {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size := by
  intro entry value finalStore completed
  let baseEntry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) origin
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) :=
    { entry with initial := entry.initial.val }
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning baseEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, ⟨reached, entry.initial.property⟩, related⟩

end LegacyBody

section Source
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before calleeHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {function : Dynamic.Closure}
  {node : ExpressionNode} {metadata : IndirectCallResolution}

/-- Raw source argument typing and original Source preservation prove the
count of this actual argument result. No execution callback is a premise. -/
theorem arguments_count_of_source_admission
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment calleeHeap ids arguments middle) :
    arguments.length = metadata.argumentCount := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type
      runtime covers locals heapTyped typed evaluated
  have reached := Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped typed evaluated.sound
  exact reached.1.length_eq.trans count

/-- The original closure application fixes its invocation dictionary. Arity
failure has no dictionary-dependent execution, so its same receipt is retained. -/
theorem call_with_closure_evidence
    {size : Nat} {invocation : Dynamic.EvidenceEnvironment} {arguments : List Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (called : RecursiveNamedCallBounds.CallOutcome program size context evidence invocation before
      (.closure function) arguments outcome after) :
    RecursiveNamedCallBounds.CallOutcome program size context evidence function.evidence before
      (.closure function) arguments outcome after := by
  cases called with
  | value applied =>
    cases applied with
    | closure same frame parameters allocation executed returned =>
      cases same
      exact .value (.closure rfl frame parameters allocation executed returned)
    | closureUnit same frame unit parameters allocation executed fellThrough =>
      cases same
      exact .value (.closureUnit rfl frame unit parameters allocation executed fellThrough)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact .fault (.closureArity mismatch)
    | closureBody same frame parameters allocation failed =>
      cases same
      exact .fault (.closureBody rfl frame parameters allocation failed)
    | closureControlEscape same frame parameters allocation executed escaped =>
      cases same
      exact .fault (.closureControlEscape rfl frame parameters allocation executed escaped)

/-- This packet is made from the actual ordered arguments and application
children of the selected Source call, preserving their separate grades. -/
theorem SourceSuffix.of_call
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {invocation : Dynamic.EvidenceEnvironment}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids
      arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence invocation middle
      (.closure function) arguments outcome after) :
    SourceSuffix program context evidence source environment before ids function argumentsSize callSize outcome after :=
  .called evaluated (call_with_closure_evidence called)

/-- The selected suffix is wrapped in the original whole parent Source rule.
Both dictionaries, the original measured callee and argument/call grades, and
all raw source metadata remain explicit. -/
theorem SourceSuffix.to_expression
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {calleeSize argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee
      (.closure function) calleeHeap)
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before call outcome after := by
  cases suffix with
  | argumentFault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]], .fault (.form (lookupExpression?_sound found) ?_)⟩
    rw [form]
    exact .indirectArguments calleeTrace trivial failed
  | called argumentsTrace called =>
    rename_i arguments middle
    have appliedArity := arguments_count_of_source_admission wellFormed runtime covers locals heapTyped typed count argumentsTrace
    obtain ⟨packed, pack⟩ := Dynamic.ValuesPack.exists_pack arguments
    cases called with
    | @value result _ applied =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize], SourceExecutionSize.stepSize []], .value (.intro (raw := result) (middle := after) (lookupExpression?_sound found) ?_ ?_)⟩
      · rw [form]
        refine .indirectCall ?_ calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity applied
        · simp [requirements, argumentCoercions, coercions, coercionRequirementIds]
        · rw [argumentCoercions]; exact .nil
      · rw [coercions]; exact .nil
    | fault failed =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize]], .fault (.form (lookupExpression?_sound found) ?_)⟩
      rw [form]
      refine .indirectApply calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity failed
      rw [argumentCoercions]; exact .nil
end Source


section Compiler
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- This packet keeps the actual hook receipt and prepared callsite. The
policy-read node is aligned with the original call occurrence explicitly. -/
structure Prepared (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered) (native : SourceCoreGeneralFunctions.CallableContext) where
  site : SourceCoreCallableContracts.Callsite
  prepared : SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id
    native.diagnostics.reasonAt = .ok site
  table : site.table = native.table
  caller : site.caller = compilation.owner
  call : site.call = id
  emitted : receipt.expression = site.lower native.diagnostics.unknown receipt.resultType receipt.calleeCode.expression
    (SourceCoreCalls.packArguments receipt.codes).expression

theorem Prepared.of_receipt
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (nodeId : receipt.node.id = id) : Nonempty (Prepared receipt native) := by
  obtain ⟨site, prepared, table, caller, call, emitted⟩ := receipt.prepared_site native active actualPolicy
  exact ⟨⟨site, prepared, table, caller, call.trans nodeId, emitted⟩⟩

private theorem guardResult_rename (reason : Option Word) (ξ : Renaming) :
    (CallableContract.guardResult reason).rename ξ = CallableContract.guardResult reason := by
  cases reason <;> rfl

private theorem dispatch_rename (gates : List CallableContract.Gate) (phase : CallableContract.Phase)
    (unknown : Word) (contract : Expr) (ξ : Renaming) :
    (CallableContract.dispatch gates phase unknown contract).rename ξ =
      CallableContract.dispatch gates phase unknown (contract.rename ξ) := by
  induction gates with
  | nil => exact guardResult_rename _ _
  | cons gate rest ih =>
    simp only [CallableContract.dispatch, Expr.rename, guardResult_rename, ih]

/-- Only static guard syntax is folded here. Renaming preserves the actual
callee, ordered argument vector and both accepted stage decisions. -/
theorem call_rename (gates : List CallableContract.Gate) (unknown : Word) (result : Ty)
    (callee arguments : Expr) (ξ : Renaming) :
    (CallableContract.call gates unknown result callee arguments).rename ξ =
      CallableContract.call gates unknown result (callee.rename ξ) (arguments.rename ξ) := by
  simp only [CallableContract.call, LanguageResult.bind, Expr.rename, dispatch_rename,
    Expr.rename_weakenAt_zero, Renaming.lift]

/-- The emitted whole parent is the exact prepared callsite after the current
runtime renaming. No arbitrary callable policy is replaced. -/
theorem Prepared.lowered_rename
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared receipt native) (ξ : Renaming) :
    lowered.expression.rename ξ = CallableContract.call prepared.site.gates native.diagnostics.unknown receipt.resultType
      (receipt.calleeCode.expression.rename ξ) ((SourceCoreCalls.packArguments receipt.codes).expression.rename ξ) := by
  have emitted : lowered.expression = receipt.expression := congrArg (fun output => output.expression) receipt.output
  rw [emitted, prepared.emitted]
  exact call_rename _ _ _ _ _ _
end Compiler


/-- Original Source metadata for this exact parent. Successful native lowering
alone does not replace the original node's requirements or coercion path. -/
structure SourceParent {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered) : Prop where
  requirements : receipt.original.requirements = []
  coercions : receipt.original.coercions = []
  arity : ids.length = metadata.argumentCount

section SelectedParent
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {callerScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (children : DataExpressionSequence.Tree source certificate callerScope ids
    (closure.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes)
  (nativeTypes : compiler.codes.map (·.type) = closure.code.receipt.loweredParameters.map Prod.snd)
  (escaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = closure.code.receipt.resultCore)
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {calleeHeap : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world calleeHeap store)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (capturesValid : FunctionValues.SourceCapturesValid calleeHeap (.closure function))
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
  {types : List TypeSystem.Ty} (sourceArguments : ExpressionsHaveTypes source context ids types)
  (sourceCount : types.length = metadata.argumentCount)

include rawResult nativeResult in
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      finalMap finalWorld function.resultType closure.code.receipt.resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases represented with
  | value related => exact .value (.compatible rawResult related)
  | fault matched => exact .fault matched

include prepared parent nativeTypes escaped rawResult nativeResult locals capturesValid
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Reflection of this accepted selected parent uses the actual callee post,
original argument/body grades and the same returned pool. Source reconstruction
uses the original parent node and independently graded child traces. -/
theorem reflects_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := closure) (codes := compiler.codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have emitted := prepared.lowered_rename compiler ξ
  rw [emitted, nativeResult] at completed
  obtain ⟨argumentsSize, callSize, outcome, after, finalMap, finalWorld, suffix, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    call_reflects_bounded_with_sequence profile closure nativeTypes escaped capturesValid callerBridge callerInitial callerStable
      budget argumentSequence bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
      calleeEvaluation stageAccepted arityAccepted completed within
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers locals heapTyped sourceArguments sourceCount calleeTrace suffix
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
    parent_result profile compiler closure rawResult nativeResult represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩


include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Reflection of this accepted selected parent uses the actual callee post,
original argument/body grades and the same returned pool. Source reconstruction
uses the original parent node and independently graded child traces. -/
theorem reflects_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_sequence profile compiler prepared parent closure nativeTypes escaped rawResult nativeResult
    locals capturesValid wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget
    (SequenceReflects.of_uniform profile closure children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace
    calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_continuations profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget argumentMeaning
      (native_continuations_of_canonical (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_receipts profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  stable wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_caller profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult
    environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning
    (fun child strict => body_reflects_to_canonical profile closure.owner closure.callerPrefix
      (closure.bodyOrigin escaped).origin (bodyMeaning child strict))
    first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation
    stageAccepted arityAccepted completed within

include prepared parent nativeTypes escaped rawResult nativeResult locals capturesValid
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Source callee and suffix receipts produce this actual emitted parent.
Arguments and called-body grades are the original inclusive Source children;
argument faults retain their reached pool without constructing a body state. -/
theorem preserves_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := closure) (codes := compiler.codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers locals heapTyped sourceArguments sourceCount calleeTrace suffix
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  cases suffix with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      call_argument_fault_preserves_bounded_with_sequence profile closure callerInitial
        budget argumentSequence first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted
        failed argumentsWithin
    refine ⟨sourceSize, .inLeft closure.code.receipt.resultCore (.word token), finalStore, finalMap, finalWorld, original, ?_, ?_, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
    · rw [emitted]; exact evaluated
    · exact parent_result profile compiler closure rawResult nativeResult (.fault matched)
  | called argumentsTrace called =>
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      call_preserves_bounded_with_sequence profile closure nativeTypes escaped capturesValid callerBridge callerInitial callerStable
        budget argumentSequence bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
        calleeEvaluation stageAccepted arityAccepted argumentsTrace argumentsWithin called callWithin
    refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, original, ?_,
      parent_result profile compiler closure rawResult nativeResult represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
    rw [emitted]; exact evaluated


include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Source callee and suffix receipts produce this actual emitted parent.
Arguments and called-body grades are the original inclusive Source children;
argument faults retain their reached pool without constructing a body state. -/
theorem preserves_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_sequence profile compiler prepared parent closure nativeTypes escaped rawResult nativeResult
    locals capturesValid wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget
    (SequencePreserves.of_uniform profile closure children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace
    calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_continuations profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget argumentMeaning
      (source_continuations_of_canonical (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_receipts profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  stable wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_caller profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult
    environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning
    (fun child strict => body_preserves_to_canonical profile closure.owner closure.callerPrefix
      (closure.bodyOrigin escaped).origin (bodyMeaning child strict))
    first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation
    stageAccepted arityAccepted suffix argumentsWithin callWithin

end SelectedParent


section AdmittedCallee
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {callerScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate callerScope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before calleeHeap : Dynamic.Heap}
  {store : Store} {ξ : Renaming} {function : Dynamic.Closure}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (stable : StableRows initial)

include certified found environments heaps locals agrees typed in
/-- Callee evaluation keeps its real post pool together with the Source heap
and lexical admission needed to type the original parent's actual arguments.
The policy-read callee node is not substituted for its original Source node. -/
theorem callee_preserves_admitted_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
    {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  obtain ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
      reached, related, reachedStable, closure⟩ :=
    callee_preserves_bounded_with_receipts profile certified found environments heaps locals agrees typed callerBridge callerInitial callerStable budget children executed smaller
  obtain ⟨captures, reachedTyped, sourceMetadata⟩ := CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped executed.sound
  exact ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reachedStable, closure, captures, Dynamic.EnvironmentAgrees.mono sourceMetadata locals, reachedTyped⟩
include certified found environments heaps locals agrees typed in
theorem callee_preserves_admitted_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
    {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  exact callee_preserves_admitted_bounded_with_receipts profile compiler certified found environments heaps locals agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

include certified found environments heaps locals agrees typed stable in
theorem callee_preserves_admitted_bounded (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
    {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : State headers keys ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        Relates initial reached ∧ StableRows reached ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  exact callee_preserves_admitted_bounded_with_caller profile compiler certified found environments heaps locals agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

end AdmittedCallee

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
