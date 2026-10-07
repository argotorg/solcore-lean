import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaNestedRuntimeBodyMeaning

/-! Lambda compiler views retain their actual named-call emission and exact
selected slots. Nested formation uses the reached owner's own history and
complete original captures, while leaving its actual pool unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}

theorem view_preserves_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix certificate))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.preserves_at_with functions owner sameLayouts conditions authorized
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed initial globals trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_preserves_bounded_with functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget argumentMeaning (bodyMeaning receipt.header receipt.member) owners receipt.member
        initial globals environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented

theorem view_reflects_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix certificate))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner compilation.administrativePrefix
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.reflects_at_with functions owner sameLayouts conditions authorized
      budget size within argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed initial globals evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_reflects_bounded_with functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget argumentMeaning (bodyMeaning receipt.header receipt.member) receipt.member
        initial globals environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩

section Formation
open CallableIndexedLambdaNestedRuntimeBodyMeaning
open RecursiveNamedLambdaFormationHeads
variable {caller : CallableIndexedOwnedFunctionValues.Header compiled program}
  {rank : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {canonical actual : Environment} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {ξ : Renaming}

/-- The real reached Current receipt supplies its own ghost. Stable lookup
uniqueness fixes the full original metadata without identifying ghost histories. -/
theorem carries_of_stable_read
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (read : store.read? owner.key.frameLocation = some (encode compiled.indexed.ancestry.layout.frame native)) :
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost metadata := by
  have encoded := Option.some.inj ((CallableIndexedOwnedFunctionEntries.reached_frame_read initial owner.position).symm.trans read)
  have current : (initial.rows owner.position).authority.current = native := by
    have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
    simpa only [decode_encode, Option.some.injEq] using decoded
  have actualHistory := (initial.rows owner.position).authority.frame.history
  rw [current] at actualHistory
  cases stable with
  | empty =>
    cases actualHistory with
    | stable carried =>
      have same := Option.some.inj (carried.lookup.symm.trans (Carries.empty (inputs := compiled.indexed.ancestry.graph.inputs) (table := compiled.indexed.ancestry.graph.table)).lookup)
      simpa only [current, same] using carried
  | state stored history =>
    cases actualHistory with
    | stable carried =>
      have same := Option.some.inj (carried.lookup.symm.trans (Carries.state stored history).lookup)
      simpa only [current, same] using carried

/-- Original canonical frame/bundle observations are combined with the exact
selected authority, including its complete ordered records and own ghost. -/
def nested_entry
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    CallableIndexedLambdaNestedFormationEntries.Entry (values := .initial compiled.compatible.checked)
      caller headers owner.key.locations 0 1 scope mapping world heap store canonical :=
  { catalog := {
      authority := {
        frameLocation := (initial.rows owner.position).authority.frameLocation
        unmapped := (initial.rows owner.position).authority.unmapped
        typed := (initial.rows owner.position).authority.typed
        current := (initial.rows owner.position).authority.current
        ghost := (initial.rows owner.position).authority.ghost
        frame := (initial.rows owner.position).authority.frame
        records := (initial.rows owner.position).authority.records
        snapshots := (initial.rows owner.position).authority.snapshots
        distinct := (initial.rows owner.position).authority.distinct
        captures := by
          intro header member
          have capture := (initial.rows owner.position).authority.captures header member
          change Nonempty (Capture headers owner.key.locations owner.key.capturePrefix
            (initial.rows owner.position).authority.frameLocation header mapping world heap store) at capture
          simpa only [prefixZero] using capture }
      globals := observed.globals }
    history := history
    bundle := bundle
    reference := by
      change canonical[scope.length + 1 + caller.globals]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type (initial.rows owner.position).authority.frameLocation)
      rw [(initial.rows owner.position).frame_eq]
      change canonical[scope.length + 1 + caller.globals]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation)
      simpa only [globals] using observed.reference }

theorem nested_entry_current
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.current =
      (initial.rows owner.position).authority.current := by
  rfl

theorem nested_entry_ghost
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.ghost =
      (initial.rows owner.position).authority.ghost := by
  rfl

theorem nested_entry_records
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.records =
      (initial.rows owner.position).authority.records := by
  rfl

theorem nested_entry_frame
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (globals : caller.globals = compiled.indexed.base.globals.length) :
    (nested_entry initial owner prefixZero observed history bundle globals).catalog.authority.frameLocation =
      owner.key.frameLocation := by
  exact (initial.rows owner.position).frame_eq

/-- Formation uses the original supported nested body and authentic current
metadata. Its native closure retains the complete actual captured environment;
formation changes neither the store nor any row's records. -/
theorem formation
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    ∃ value,
      Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
        environment heap id (.closure (formed head environment)) heap ∧
      Evaluates actual store (lowered.expression.rename ξ) (.inRight .word value) store ∧
      CompatiblePayload.ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
        mapping world head.code.sourceNode.type (.closure (formed head environment)) value lowered.type ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, mapping, world, heap, store, canonical⟩ := by
  let entry := nested_entry initial owner prefixZero observed history bundle globals
  let captured : Captures compiled.indexed mapping world scope environment actual :=
    captures_for complete globals entry related agrees typed
  let code : Code compiled.indexed (formed head environment) scope captured.administrative := actualCode head environment
  let currentHistory : History code := historyAt head entry environment
  let body : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code := actualSupport head environment
  have origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code currentHistory body :=
    CallableIndexedOwnedFunctionValues.ActualSourceOrigin.of_nested head entry environment
  have captureGlobals := capture_globals_for complete globals slots entry related agrees typed
  have captureGlobals' : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    have frame : entry.catalog.authority.frameLocation = owner.key.frameLocation := by
      exact (initial.rows owner.position).frame_eq
    simpa only [frame] using captureGlobals
  have current : (initial.rows owner.position).authority.current = currentHistory.native := by
    rfl
  have ghost : (initial.rows owner.position).authority.ghost = currentHistory.ghost := by
    rfl
  obtain ⟨sourceValue, native, represented, _determined⟩ :=
    CallableIndexedOwnedFunctionValues.lambda_of_formation (compiled := compiled) (program := program)
      (headers := headers) (keys := keys) (function := formed head environment) initial owner captured code currentHistory body origin
      captureGlobals' (reference_index head) current ghost profile stored
      (by change Dynamic.OrdinaryRequirementLayout head.code.sourceNode.requirements head.code.sourceNode.coercions []
          rw [head.requirements, head.coercions]; rfl) head.coercions
  refine ⟨CallableIndexedLambdaValues.value code captured.embedding currentHistory.native actual, ?_, ?_, ?_,
    ProtectedStateTransition.Transition.refl (protocol headers keys) initial⟩
  · change Dynamic.ExpressionEvaluates program context evidence (CallableIndexedNamedGeneration.source caller.named)
      environment heap head.code.id (.closure (formed head environment)) heap at sourceValue
    simpa only [head.identifier] using sourceValue
  · exact Eq.mp (congrArg (fun expression => Evaluates actual store expression
      (.inRight .word (CallableIndexedLambdaValues.value code captured.embedding currentHistory.native actual)) store)
      (congrArg (fun output : SourceCoreBasic.LoweredExpr => output.expression.rename ξ) head.emitted)) native
  · rw [head.sourceType, head.nativeType]
    exact .function represented

theorem formation_preserves
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    (unique : NodeOccurrencesUnique source) {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let code : Code compiled.indexed (formed head environment) scope (nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller) := actualCode head environment
  have emptyCoercions : code.sourceNode.coercions = [] := head.coercions
  rw [sameSource] at unique trace
  cases trace.sound with
  | value evaluated =>
    rename_i result
    have original : Dynamic.ExpressionEvaluates program (formed head environment).context (formed head environment).evidence
        (formed head environment).source (formed head environment).captured heap code.id result after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using evaluated
    obtain ⟨rfl, rfl⟩ := source_value_of_code (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := program) (function := formed head environment) (scope := scope) (administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller)
      code unique emptyCoercions original
    obtain ⟨value, _source, native, represented, transition⟩ :=
      formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed heaps.runtime_hasTypes
    exact ⟨.inRight .word value, store, mapping, world, native, .value represented, heaps,
      .refl _, .refl _, .refl _ _, .refl _, transition⟩
  | fault failed =>
    rename_i reason
    have original : Dynamic.ExpressionFaults program (formed head environment).context (formed head environment).evidence
        (formed head environment).source (formed head environment).captured heap code.id reason after := by
      simpa only [code, actualCode, recaptureCode, formed, CallableIndexedLambdaGeneration.closure, head.identifier] using failed
    exact False.elim (excludes_fault_of_code (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := program) (function := formed head environment) (scope := scope) (administrative := nativePrefix (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program) caller)
      code unique emptyCoercions original)

theorem formation_reflects
    (head : LambdaAt (values := .initial compiled.compatible.checked) headers caller registry faults rank
      source context evidence scope id lowered)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
    (globals : caller.globals = compiled.indexed.base.globals.length)
    (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
    (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (prefixZero : owner.key.capturePrefix = 0)
    (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations 1 scope canonical owner.key.frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows owner.position).authority.current (initial.rows owner.position).authority.ghost
      (some (CallableIndexedNamedGeneration.state caller.named)))
    (bundle : (canonical.map Value.type)[scope.length]? = some caller.named.signature.parameterType)
    (related : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world heap store)
    (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment heap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld head.code.sourceNode.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨nativeValue, sourceValue, native, represented, transition⟩ :=
    formation head profile complete globals slots initial owner prefixZero observed history bundle related agrees typed heaps.runtime_hasTypes
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound native
  have original : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id
      (.value (.closure (formed head environment))) heap := by
    simpa only [sameSource] using (Dynamic.ExpressionEvaluatesOutcome.value sourceValue)
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size original
  exact ⟨sourceSize, _, heap, mapping, world, sized, .value represented, heaps,
    .refl _, .refl _, .refl _ _, .refl _, transition⟩

end Formation
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaViewHeads
