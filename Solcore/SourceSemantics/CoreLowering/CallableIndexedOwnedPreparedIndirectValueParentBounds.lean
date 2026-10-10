import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueSourceSuffix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredIndirectCallForModelReflection

/-! One accepted indirect parent at the literal callee value. The actual
positive callee relation selects closure/global/builtin payload application;
the same ordered E argument fold and original four-bind inversion retain all
reached states and independent grades. Application ports are instantiated by
that concrete dispatcher, not stored in static qualification.

The gate inputs are the exact two native acceptance conclusions of the
authentic user/builtin boundary decision, with the same contracted carrier.
Stage/arity rejection have separate boundary outcomes. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters CallableIndexedOwnedIndirectExpressionHeads
open CallableIndexedOwnedStoredClosureArgumentReceipts CallableIndexedOwnedStoredIndirectCallBounds
open CallableIndexedOwnedPreparedIndirectValueSourceSuffix
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

section Selected
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique source)
  (parentTyped : ExpressionHasType source context id compiler.original.type)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  {firstMap mapping : LocationMap} {firstWorld world : StoreTyping}
  {before calleeHeap : Dynamic.Heap} {firstStore store : Store}
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
  (first : callerProtocol.State ⟨scope, firstMap, firstWorld, before, firstStore, canonical⟩)
  (firstAdmission : Admission bridge context first)
  (calleeState : callerProtocol.State ⟨scope, mapping, world, calleeHeap, store, canonical⟩)
  (calleeRelated : callerProtocol.Relates first calleeState)
  (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
  (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
  (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
  {function : Dynamic.Value} {invocation : Dynamic.EvidenceEnvironment} {sourceResultType : TypeSystem.Ty} {calleeNative : Value}
  (callable : Dynamic.CallableValue function)
  {parameterCore resultCore : Ty}
  (nativeTyped : RuntimeValueHasType world calleeNative (CallableContract.functionType parameterCore resultCore) compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world calleeHeap store)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType sourceResultType)
  (nativeResult : compiler.resultType = resultCore)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {calleePayload : Value} {contract : Word}
  (shape : calleeNative = .pair calleePayload (.word contract))
  (firstGate : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown contract = none)
  (secondGate : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown contract = none)
  {calleeSize : Nat}
  (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
    context evidence source environment before callee function calleeHeap)
  (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

/-- The whole parent keeps the actual returned caller witness and success-only
Source admission. Its native and Source result types remain independent receipts. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (value : Value) (finalStore : Store)
    (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
  AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
    callerProtocol.Relates first reached ∧ PostAdmission bridge context compiler.original.type outcome reached

include rawResult nativeResult in
theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (related : FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents model finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases related with
  | value payload => exact .value (.compatible rawResult payload)
  | fault matched => exact .fault matched

/-- A genuine called constructor at the same Source suffix and its exact grade. -/
def CalledSuffix {suffixArgumentsSize suffixCallSize : Nat}
    {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∃ (arguments : List Dynamic.Value) (middle : Dynamic.Heap),
    ∃ argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) suffixArgumentsSize
      context evidence source environment calleeHeap ids arguments middle,
    ∃ called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) suffixCallSize
      context evidence invocation middle function arguments suffixOutcome suffixAfter,
      suffix = .called argumentsTrace called

/-- An intermediate leaf at the actual admitted argument state. The final
prepared endpoint constructs this leaf from strict body children. -/
def ApplicationPreserves (budget : Nat)
    {suffixArgumentsSize suffixCallSize : Nat} {suffixOutcome : Dynamic.ExpressionOutcome} {suffixAfter : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      suffixArgumentsSize suffixCallSize suffixOutcome suffixAfter) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∀ {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap},
    (argumentsTrace : SourceExecutionSize.ExpressionsEvaluate (Program.ofChecked compiled.sourceProgram) argumentsSize context evidence
      source environment calleeHeap ids arguments middle) →
    (called : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize context evidence
      invocation middle function arguments outcome after) →
    CalledSuffix (context := context) (evidence := evidence) (environment := environment) suffix →
    callSize ≤ budget →
    ∃ result finalStore finalMap finalWorld,
      Evaluates [calleeNative, DataPatternValues.packValues payloads] middleStore
        CallableIndexedLambdaCalls.applyPayload result finalStore ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends middleMap finalMap ∧ WorldExtends middleWorld finalWorld ∧
      AdministrativePreserved middleMap middleStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend middle after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates argumentState returned

/-- The native application port is instantiated by the same concrete value
dispatcher. This is a strict F induction step at the actual argument state. -/
def ApplicationReflects (budget : Nat) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping} {middle : Dynamic.Heap} {middleStore : Store}
    {arguments : List Dynamic.Value} {payloads : List Value} {types : List TypeSystem.Ty}
    {parameter sourceResult : TypeSystem.Ty} {packed : Dynamic.Value},
    (argumentState : callerProtocol.State ⟨scope, middleMap, middleWorld, middle, middleStore, canonical⟩) →
    Admission bridge context argumentState →
    LocationMap.Extends mapping middleMap → WorldExtends world middleWorld →
    AdministrativePreserved mapping store middleMap middleStore → Dynamic.HeapMetadataExtend calleeHeap middle →
    Dynamic.ValueHasType context calleeHeap function (.function parameter sourceResult) →
    Dynamic.HeapTypesExtend calleeHeap middle →
    DataExpressionSequence.Values model middleMap middleWorld sourceTypes (compiler.codes.map (·.type)) arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions middleMap middleWorld middle middleStore →
    Dynamic.ValuesHaveTypes context middle arguments types → Dynamic.ValuesPack arguments packed →
    TypeSystem.Ty.productMany types = parameter →
    ∀ {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size [calleeNative, DataPatternValues.packValues payloads] middleStore
      CallableIndexedLambdaCalls.applyPayload value finalStore → size ≤ budget →
    ∃ callSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) callSize context evidence
        invocation middle function arguments outcome after ∧
      FunctionCalls.ResultRepresents model finalMap finalWorld sourceResultType resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends middleMap finalMap ∧ WorldExtends middleWorld finalWorld ∧
      AdministrativePreserved middleMap middleStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend middle after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates argumentState returned


include parent tree unique parentTyped wellFormed runtime covers environments locals agrees typed firstAdmission
  calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata nativeTyped heaps
  rawResult nativeResult callable shape firstGate secondGate calleeTrace calleeEvaluation in
/-- A real successful callee post feeds ordered admitted arguments, the exact
parameter continuation and the original whole call. Only strict child IH remains. -/
theorem preserves_with_application
    (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected sidecar prepared.site callee ids metadata compiler.original row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
      bridge model context evidence source certificate faults size)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : Suffix (Program.ofChecked compiled.sourceProgram) context evidence invocation source environment calleeHeap ids function
      argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget)
    (applicationPreserves : ApplicationPreserves (registry := registry) (faults := faults) bridge functions compiler
      (context := context) (evidence := evidence) (environment := environment) (scope := scope) (canonical := canonical) (calleeHeap := calleeHeap)
      (mapping := mapping) (world := world) (store := store) (function := function)
      (calleeNative := calleeNative) (sourceTypes := sourceTypes) (resultCore := resultCore) (sourceResultType := sourceResultType) budget suffix) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) (context := context) bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      function (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
    argumentsTyping count calleeTrace suffix
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons nativeTyped (typed.weaken calleeWorlds))
  cases suffix with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
        frame, metadata, reached, related, _stable⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_fault_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission failed argumentsWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    have whole := call_argument_fault (resultType := resultCore) shape calleeEvaluation firstGate evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, _, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
      calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
      reached, callerProtocol.trans calleeRelated related,
      after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | called argumentsTrace called =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentAdmission⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.preserves_values_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace argumentsWithin
    obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
      after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping argumentsTrace
    obtain ⟨result, finalStore, finalMap, finalWorld, evaluated, resultRep, finalHeaps, lastMaps, lastWorlds,
        lastFrame, lastMetadata, returned, lastRelated⟩ :=
      applicationPreserves argumentState argumentAdmission maps worlds frame metadata calleeTyped extension
        represented middleHeaps rawTyped packing (empty_bundle application compiler.argumentCoercions)
        argumentsTrace called ⟨_, _, argumentsTrace, called, rfl⟩ callWithin
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentEvaluation
    have whole := call_payload_success (resultType := resultCore) shape calleeEvaluation firstGate
      argumentEvaluation secondGate evaluated
    rw [← emitted] at whole
    exact ⟨sourceSize, result, finalStore, finalMap, finalWorld, original, whole,
      parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
      (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
      (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
      returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
      after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
        ((calleeFrame.trans frame).trans lastFrame)⟩

include unique parentTyped in
/-- The original finite whole-call inversion retains independent Source/native
grades. Argument faults keep the actual child post; successful arguments call the
receiving-model payload reflector once at their genuine reached state. -/
theorem reflects_with_application
    (parent : SourceParent compiler)
    (tree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
    (covers : evidence.Covers context)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      firstMap firstWorld administrative scope environment canonical compiled.indexed.layouts.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes firstWorld actual actualContext compiled.indexed.layouts.definitions)
    (firstAdmission : Admission bridge context first)
    (calleeRelated : callerProtocol.Relates first calleeState)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend before calleeHeap)
    (nativeTyped : RuntimeValueHasType world calleeNative (CallableContract.functionType parameterCore resultCore) compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world calleeHeap store)
    (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType sourceResultType)
    (nativeResult : compiler.resultType = resultCore)
    (callable : Dynamic.CallableValue function)
    (shape : calleeNative = .pair calleePayload (.word contract))
    (firstGate : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown contract = none)
    (secondGate : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown contract = none)
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) calleeSize
      context evidence source environment before callee function calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word calleeNative) store)
    (_selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
      sidecar prepared.site callee ids metadata compiler.original row)
    (budget : Nat)
    (children : ∀ size, size < budget → CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
      bridge model context evidence source certificate faults size)
    (applicationReflects : ApplicationReflects (registry := registry) (faults := faults)
      (context := context) (evidence := evidence) (invocation := invocation) (function := function)
      (scope := scope) (canonical := canonical) (mapping := mapping) (world := world) (store := store)
      (calleeHeap := calleeHeap) (calleeNative := calleeNative) (sourceTypes := sourceTypes)
      (sourceResultType := sourceResultType) (resultCore := resultCore)
      bridge functions compiler budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize context evidence source
        environment before id outcome after ∧
      ResultAt
        (registry := registry) (faults := faults) (context := context)
        bridge functions compiler first outcome after value finalStore finalMap finalWorld := by
  obtain ⟨parameter, sourceResult, rawTypes, calleeTyping, argumentsTyping, application⟩ :=
    original_facts unique compiler.found compiler.originalForm parentTyped
  obtain ⟨calleeTyped, calleeHeapTyped, _calleeExtension⟩ :=
    wellFormed.wholeLanguagePreservation.expression context evidence source environment before calleeHeap callee
      function (.function parameter sourceResult) runtime covers locals firstAdmission.heap calleeTyping calleeTrace.sound
  have calleeAdmission : Admission bridge context calleeState :=
    ⟨calleeHeapTyped, StableRows.after_administrative (bridge.pool first) (bridge.pool calleeState) firstAdmission.rows calleeFrame⟩
  have count : rawTypes.length = metadata.argumentCount := by cases application with | intro count _ _ _ => exact count.symm
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  rw [emitted] at completed
  have layout : EnvironmentsAgree ((Renaming.insertion 0).comp ((Renaming.insertion 0).comp ξ)) canonical (.unit :: calleeNative :: actual) :=
    GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees calleeNative) .unit
  have actualTyped := RuntimeEnvironmentHasTypes.cons RuntimeValueHasType.unit
    (RuntimeEnvironmentHasTypes.cons nativeTyped (typed.weaken calleeWorlds))
  cases accepted_completed shape calleeEvaluation firstGate secondGate completed within with
  | failed argumentsTrace smaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, after, finalMap, finalWorld, sourceArguments, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, _post⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases sourceArguments with
      | fault failed =>
        obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (Suffix.argumentFault failed)
        exact ⟨sourceSize, _, after, finalMap, finalWorld, original,
          parent_result functions compiler rawResult nativeResult (.fault matched), finalHeaps,
          calleeMaps.trans maps, calleeWorlds.trans worlds, calleeFrame.trans frame, calleeMetadata.trans metadata,
          reached, callerProtocol.trans calleeRelated related,
          after_expression_sized first reached firstAdmission wellFormed runtime covers locals parentTyped original (calleeFrame.trans frame)⟩
  | applied argumentsTrace applicationTrace smaller applicationSmaller =>
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨argumentsSize, argumentsOutcome, middle, middleMap, middleWorld, sourceArguments, represented, middleHeaps,
        maps, worlds, frame, metadata, argumentState, related, argumentPost⟩ :=
      CallableIndexedOwnedAdmittedExpressionSequence.reflects_bounded bridge budget tree unique argumentsTyping children
        (environments.extend calleeMaps calleeWorlds) heaps (locals.mono calleeMetadata) layout actualTyped
        calleeState calleeAdmission argumentsTrace smaller
    cases represented with
    | values represented =>
      cases sourceArguments with
      | values sourceArguments =>
        obtain ⟨packed, packing, rawTyped, _heapTyped, extension, _packedTyped⟩ :=
          after_trace wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped argumentsTyping sourceArguments
        obtain ⟨callSize, outcome, after, finalMap, finalWorld, called, resultRep, finalHeaps, lastMaps, lastWorlds,
            lastFrame, lastMetadata, returned, lastRelated⟩ :=
          applicationReflects argumentState (argumentPost.successful _ rfl) maps worlds frame metadata
            calleeTyped extension represented middleHeaps rawTyped packing
            (empty_bundle application compiler.argumentCoercions) applicationTrace (Nat.le_of_lt applicationSmaller)
        obtain ⟨sourceSize, original⟩ := Suffix.to_expression (invocation := invocation) compiler.found compiler.originalForm parent.requirements parent.coercions
          compiler.argumentCoercions parent.arity callable wellFormed runtime covers (locals.mono calleeMetadata) calleeHeapTyped
          argumentsTyping count calleeTrace (Suffix.called sourceArguments called)
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
          parent_result functions compiler rawResult nativeResult resultRep, finalHeaps,
          (calleeMaps.trans maps).trans lastMaps, (calleeWorlds.trans worlds).trans lastWorlds,
          (calleeFrame.trans frame).trans lastFrame, (calleeMetadata.trans metadata).trans lastMetadata,
          returned, callerProtocol.trans (callerProtocol.trans calleeRelated related) lastRelated,
          after_expression_sized first returned firstAdmission wellFormed runtime covers locals parentTyped original
            ((calleeFrame.trans frame).trans lastFrame)⟩
end Selected
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedIndirectValueParentBounds
