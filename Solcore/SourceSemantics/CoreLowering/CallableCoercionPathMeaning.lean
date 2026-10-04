import Solcore.SourceSemantics.CoreLowering.CallableCoercionMethodEntries

/-! Ordered coercion paths reuse the concrete method body theorem. The forward
trace records the actual selected dictionaries; it is a restricted annotation
of independent source body derivations. Reflection constructs ordinary source
path judgments. Neither direction assumes a universal method-body meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning
open SourceCoreCallableIndexedFrames CallableCoercionMethodEntries

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {values : ValuesContext} {program : SourceSemantics.Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment}
abbrev MethodProfile := Method prepared values program context evidence
abbrev Profiles := List (MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence))

/-- Raw source endpoints and native slots compose separately. Projection alone
cannot identify the source types. These are static layout equations. -/
inductive Chain : TypeSystem.Ty → Ty → Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence) → TypeSystem.Ty → Ty → Prop where
  | nil (source : TypeSystem.Ty) (native : Ty) : Chain source native [] source native
  | cons {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
      {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)} {target : TypeSystem.Ty} {native : Ty}
      (tail : Chain method.step.target method.call.signature.resultType methods target native) :
      Chain method.step.source method.call.signature.parameterType (method :: methods) target native

/-- The annotation retains independent BodyInvokes/BodyFaults at the specific
selected body and dictionary. Its erasure is the existing source path judgment;
there is no evidence-uniqueness claim for arbitrary source derivations. -/
inductive SelectedTrace : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence) →
    Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | nil {heap input} : SelectedTrace [] heap input (.value input) heap
  | cons {method methods before middle after input value outcome}
      (body : Dynamic.BodyInvokes program method.sourceBody method.function.evidence before [input] value middle)
      (tail : SelectedTrace methods middle value outcome after) :
      SelectedTrace (method :: methods) before input outcome after
  | fault {method methods before after input reason}
      (body : Dynamic.BodyFaults program method.sourceBody method.function.evidence before [input] reason after) :
      SelectedTrace (method :: methods) before input (.fault reason) after

def PathOutcome (methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence))
    (before : Dynamic.Heap) (input : Dynamic.Value) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) : Prop :=
  match outcome with
  | .value result => Dynamic.CoercionPathExecutes program context evidence before (methods.map (·.step)) input result after
  | .fault reason => Dynamic.CoercionPathFaults program context evidence before (methods.map (·.step)) input reason after

theorem SelectedTrace.sound {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {before after : Dynamic.Heap} {input : Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (trace : SelectedTrace methods before input outcome after) : PathOutcome methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | @cons method methods before middle after input value outcome invoked tail ih =>
    cases outcome with
    | value result => exact .cons (.method method.selected invoked) ih
    | fault reason => exact .tail (.method method.selected invoked) ih
  | @fault method methods before after input reason failed => exact .head (.method method.selected failed)

variable {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (definitions : prepared.layouts.definitions = ambient.definitions)
  (registered : prepared.ancestry.layout.frame.Registered ambient.definitions)
  {faults : FunctionCalls.FaultRep} {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {methods : Profiles (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
  (uninitialized : ∀ method ∈ methods, ∀ id location, faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
  (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))

private theorem arguments {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    {mapping : LocationMap} {world : StoreTyping} {input : Dynamic.Value} {native : Value}
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType) :
    Arguments (CompatibleAmbientHeap.payloadModel values.checked registry functions) mapping world method.named.inputs [input] [native] := by
  rw [method.bindings]
  apply Arguments.cons _ Arguments.nil
  change ValueRep _ _ _ _ _ method.input.scheme.body _ _ _
  simpa only [method.inputType] using represented

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- One reached call consumes only concrete body semantics. All future captures
are transported from actual administrative preservation. -/
theorem method_preserves {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    {outcome : Dynamic.ExpressionOutcome} (trace : BodyOutcome program method.sourceBody method.function.evidence before [input] outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨value, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_preserves (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := method.valid)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := method.frame)
      rfl rfl rfl capture.installed trace
  exact ⟨value, finalStore, finalMap, finalWorld, invoked, by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
theorem method_reflects {method : MethodProfile (prepared := prepared) (values := values) (program := program) (context := context) (evidence := evidence)}
    (member : method ∈ methods) {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world method.step.source input native method.call.signature.parameterType)
    (completed : CallableCoercionSpine.Invoke caller reason method.call store (.inRight .word native) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program method.sourceBody method.function.evidence before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        method.step.target method.call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨capture⟩ := entry.captures method member
  have parameterEq : method.function.parameters = method.named.inputs.map Prod.fst := by simp only [method.parameters, method.bindings, List.map_cons, List.map_nil]
  have inputEq : method.function.source.inputs = method.named.inputs.map Prod.fst := by simp only [method.inputs, method.bindings, List.map_cons, List.map_nil]
  have parametersCompiled := method.compiled.parametersCompiled
  rw [← method.source] at parametersCompiled
  have reference : (native :: capture.captured)[capture.embedding.lift (prepared.base.globals.length + 1)]? =
      some (.cellRef prepared.ancestry.layout.frame.type entry.frameLocation) := by
    simpa only [Renaming.lift, Nat.succ_sub_one, List.getElem?_cons_succ] using capture.capturedReference
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, _, _⟩ :=
    CallableCoercionMethodBody.invoke_reflects (prepared := prepared.ancestry) (functions := functions)
      (extension := extension) (program := program) (onError := allocationError) (certificate := method.certificate)
      (parameters := parameterEq) (inputs := inputEq) (extended := method.extended) (contextValid := method.valid)
      (unique := method.unique) (uninitialized := uninitialized method member) (missing := missing method member)
      (faithful := faithful) (functionLeaves := observations) (functionTypes := runtimeViews)
      (acceptedPrefix := parametersCompiled) (definitions := definitions) (registered := registered)
      (acceptedHook := method.compiled.hook) (represented := arguments functions represented)
      (environments := capture.environments) (heaps := heaps) (initialLocals := capture.locals)
      (actualLayout := by
        intro index value found
        exact Core.ReadOnly.EnvironmentsAgree.lift capture.layout native found)
      (actualTyped := .cons represented.runtime_hasType capture.typed)
      (canonicalReference := capture.reference) (actualReference := reference) (unmapped := entry.unmapped)
      (typed := entry.typed) (caller := entry.frame) (snapshots := entry.snapshots) (sourceFrame := method.frame)
      rfl rfl rfl capture.installed completed
  exact ⟨outcome, after, finalMap, finalWorld, trace, by simpa only [method.result, method.signature] using related,
    finalHeaps, maps, worlds, frame, metadata, ⟨entry.extend maps worlds frame metadata⟩⟩

theorem Chain.final_type {source target : TypeSystem.Ty} {input output : Ty}
    (chain : Chain source input methods target output) :
    CallableCoercionSpine.finalType input (methods.map (·.call)) = output := by
  induction chain with
  | nil => rfl
  | cons tail ih => exact ih

/-- Failure inversion follows the actual ordered native calls, so every
unreached method keeps both the payload and the exact failure store. -/
theorem failed_runs {caller : Environment} {reason : Word} {store finalStore : Store}
    {tag : Ty} {payload value : Value} {calls : List CallableCoercionSpine.Call}
    (runs : CallableCoercionSpine.Runs caller reason store (.inLeft tag payload) calls value finalStore) :
    value = .inLeft (CallableCoercionSpine.finalType tag calls) payload ∧ finalStore = store := by
  generalize inputEq : Value.inLeft tag payload = input at runs
  induction runs generalizing tag with
  | nil => cases inputEq; exact ⟨rfl, rfl⟩
  | cons head tail ih =>
    cases inputEq
    cases head with
    | skipped => exact ih rfl

section Common

/-- The source and native endpoints of one actual ordered method row. Concrete
body receipts and saved entries stay in the caller's row type. -/
structure Row where
  step : CoercionStep
  call : CallableCoercionSpine.Call
  body : Dynamic.BodyInstance
  dictionary : Dynamic.EvidenceEnvironment

inductive ChainFor {α : Type} (row : α → Row) :
    TypeSystem.Ty → Ty → List α → TypeSystem.Ty → Ty → Prop where
  | nil (source : TypeSystem.Ty) (native : Ty) : ChainFor row source native [] source native
  | cons {method : α} {methods : List α} {target : TypeSystem.Ty} {native : Ty}
      (tail : ChainFor row (row method).step.target (row method).call.signature.resultType methods target native) :
      ChainFor row (row method).step.source (row method).call.signature.parameterType (method :: methods) target native

inductive SelectedTraceFor {α : Type} (row : α → Row) (program : Program) :
    List α → Dynamic.Heap → Dynamic.Value → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | nil {heap input} : SelectedTraceFor row program [] heap input (.value input) heap
  | cons {method methods before middle after input value outcome}
      (body : Dynamic.BodyInvokes program (row method).body (row method).dictionary before [input] value middle)
      (tail : SelectedTraceFor row program methods middle value outcome after) :
      SelectedTraceFor row program (method :: methods) before input outcome after
  | fault {method methods before after input reason}
      (body : Dynamic.BodyFaults program (row method).body (row method).dictionary before [input] reason after) :
      SelectedTraceFor row program (method :: methods) before input (.fault reason) after

variable {α : Type} {row : α → Row}

theorem ChainFor.final_type {source target : TypeSystem.Ty} {input output : Ty} {methods : List α}
    (chain : ChainFor row source input methods target output) :
    CallableCoercionSpine.finalType input (methods.map (fun method => (row method).call)) = output := by
  induction chain with
  | nil => rfl
  | cons tail ih => exact ih

variable {State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type}
  {caller : Environment} {reason : Word}

/-- Internal one-step continuation for the shared ordered proof. A public
concrete consumer supplies it from its actual static body certificate. -/
def StepPreservesFor (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program) (caller : Environment) (reason : Word) (methods : List α) : Prop :=
  ∀ {method mapping world before after store input native outcome}, method ∈ methods →
    State mapping world before store →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    BodyOutcome program (row method).body (row method).dictionary before [input] outcome after →
    ∃ result finalStore finalMap finalWorld,
      CallableCoercionSpine.Invoke caller reason (row method).call store (.inRight .word native) result finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome result ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore)

theorem preserves_for
    (extendState : ∀ {mapping nextMap world nextWorld before after store finalStore},
      State mapping world before store → LocationMap.Extends mapping nextMap → WorldExtends world nextWorld →
      AdministrativePreserved mapping store nextMap finalStore → Dynamic.HeapMetadataExtend before after →
      State nextMap nextWorld after finalStore)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepPreservesFor row State functions registry faults program caller reason methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {input : Dynamic.Value} {native : Value} {outcome : Dynamic.ExpressionOutcome}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (trace : SelectedTraceFor row program methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  induction chain generalizing mapping world before after store input native outcome with
  | nil source type =>
    cases trace
    exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry⟩⟩
  | @cons method rest target output chain ih =>
    cases trace with
    | @cons _ _ _ middle _ _ value _ body tail =>
      obtain ⟨result, middleStore, middleMap, middleWorld, invoked, related, middleHeaps, maps, worlds, frame, metadata, ⟨nextEntry⟩⟩ :=
        step (List.mem_cons_self) entry heaps represented (.value body)
      cases related with
      | value middleRepresented =>
        obtain ⟨result, finalStore, finalMap, finalWorld, runs, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, _⟩ :=
          ih (fun member => step (List.mem_cons_of_mem _ member)) nextEntry middleHeaps middleRepresented tail
        exact ⟨_, _, _, _, .cons invoked runs, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
          frame.trans tailFrame, metadata.trans tailMetadata,
          ⟨extendState entry (maps.trans tailMaps) (worlds.trans tailWorlds) (frame.trans tailFrame) (metadata.trans tailMetadata)⟩⟩
    | fault body =>
      obtain ⟨result, finalStore, finalMap, finalWorld, invoked, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
        step (List.mem_cons_self) entry heaps represented (.fault body)
      cases related with
      | fault faultRep =>
        refine ⟨_, _, _, _, .cons invoked (CallableCoercionSpine.Runs.failure caller reason finalStore _ _ _),
          ?_, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
        rw [chain.final_type]
        exact .fault faultRep

def StepReflectsFor (row : α → Row)
    (State : LocationMap → StoreTyping → Dynamic.Heap → Store → Type)
    (functions : FunctionModel values.checked.catalog ambient)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (program : Program)
    (invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop) (methods : List α) : Prop :=
  ∀ {method mapping world before store finalStore input native value}, method ∈ methods →
    State mapping world before store →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    ValueRep values.checked registry functions mapping world (row method).step.source input native
      (row method).call.signature.parameterType →
    invocation (row method).call store (.inRight .word native) value finalStore →
    ∃ outcome after finalMap finalWorld,
      BodyOutcome program (row method).body (row method).dictionary before [input] outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        (row method).step.target (row method).call.signature.resultType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore)

theorem reflects_for
    {invocation : CallableCoercionSpine.Call → Store → Value → Value → Store → Prop}
    (forget : ∀ {call before input result after}, invocation call before input result after →
      CallableCoercionSpine.Invoke caller reason call before input result after)
    (extendState : ∀ {mapping nextMap world nextWorld before after store finalStore},
      State mapping world before store → LocationMap.Extends mapping nextMap → WorldExtends world nextWorld →
      AdministrativePreserved mapping store nextMap finalStore → Dynamic.HeapMetadataExtend before after →
      State nextMap nextWorld after finalStore)
    {source target : TypeSystem.Ty} {inputType outputType : Ty} {methods : List α}
    (step : StepReflectsFor row State functions registry faults program invocation methods)
    (chain : ChainFor row source inputType methods target outputType)
    {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : State mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.RunsFor invocation store (.inRight .word native) (methods.map (fun method => (row method).call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTraceFor row program methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (State finalMap finalWorld after finalStore) := by
  induction chain generalizing mapping world before store input native value finalStore with
  | nil source type =>
    cases runs
    exact ⟨_, _, _, _, .nil, .value represented, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨entry⟩⟩
  | @cons method rest target output chain ih =>
    cases runs with
    | cons invoked tail =>
      obtain ⟨outcome, middle, middleMap, middleWorld, body, related, middleHeaps, maps, worlds, frame, metadata, ⟨nextEntry⟩⟩ :=
        step (List.mem_cons_self) entry heaps represented invoked
      cases related with
      | value middleRepresented =>
        obtain ⟨outcome, after, finalMap, finalWorld, traced, related, finalHeaps, tailMaps, tailWorlds, tailFrame, tailMetadata, _⟩ :=
          ih (fun member => step (List.mem_cons_of_mem _ member)) nextEntry middleHeaps middleRepresented tail
        have invoked := by cases body with | value body => exact body
        exact ⟨_, _, _, _, .cons invoked traced, related, finalHeaps, maps.trans tailMaps, worlds.trans tailWorlds,
          frame.trans tailFrame, metadata.trans tailMetadata,
          ⟨extendState entry (maps.trans tailMaps) (worlds.trans tailWorlds) (frame.trans tailFrame) (metadata.trans tailMetadata)⟩⟩
      | fault faultRep =>
        obtain ⟨rfl, rfl⟩ := failed_runs (tail.map forget).toRuns
        have failed := by cases body with | fault body => exact body
        refine ⟨_, _, _, _, .fault failed, ?_, middleHeaps, maps, worlds, frame, metadata, ⟨nextEntry⟩⟩
        rw [chain.final_type]
        exact .fault faultRep


end Common


/-- The legacy receipt keeps exactly the same selected row in the common path. -/
def MethodProfile.row (method : MethodProfile (prepared := prepared) (values := values)
    (program := program) (context := context) (evidence := evidence)) : Row :=
  ⟨method.step, method.call, method.sourceBody, method.function.evidence⟩

theorem Chain.toFor {source target : TypeSystem.Ty} {input output : Ty}
    (chain : Chain source input methods target output) :
    ChainFor MethodProfile.row source input methods target output := by
  induction chain with
  | nil => exact .nil _ _
  | cons tail ih => exact .cons ih

theorem SelectedTrace.toFor {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after) :
    SelectedTraceFor MethodProfile.row program methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | cons body tail ih => exact .cons body ih
  | fault body => exact .fault body

theorem SelectedTrace.ofFor {before after : Dynamic.Heap} {input : Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (trace : SelectedTraceFor MethodProfile.row program methods before input outcome after) :
    SelectedTrace methods before input outcome after := by
  induction trace with
  | nil => exact .nil
  | cons body tail ih => exact .cons body ih
  | fault body => exact .fault body

include extension definitions registered faithful observations runtimeViews in
/-- Forward preservation uses independent body traces at the actual selected
method dictionaries. Arbitrary source dictionaries need a separate coherence
or evidence-independence theorem. -/
theorem preserves (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after)
    (reason : Word) :
    ∃ value finalStore finalMap finalWorld,
      CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  exact preserves_for (functions := functions)
    (State := Entry methods ambient.definitions caller)
    (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
    (fun member entry heaps represented trace =>
      method_preserves functions extension definitions registered faithful observations runtimeViews
        uninitialized missing member entry heaps represented trace reason)
    chain.toFor entry heaps represented trace.toFor

include extension definitions registered faithful observations runtimeViews in
/-- Every completed native path reconstructs an independent source path with
its actual selected dictionaries. It needs no source completion premise. -/
theorem reflects (uninitialized : ∀ method ∈ methods, ∀ id location,
      faults (.uninitializedLocation location) (method.diagnostics.reasonAt method.named.signature.key id))
    (missing : ∀ method ∈ methods, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
      faults (.missingMappingDefault value) ((method.diagnostics.reasonAt method.named.signature.key id).add tag))
    {source target : TypeSystem.Ty} {inputType outputType : Ty}
    (chain : Chain source inputType methods target outputType)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {store finalStore : Store} {input : Dynamic.Value} {native value : Value} {reason : Word}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputType)
    (runs : CallableCoercionSpine.Runs caller reason store (.inRight .word native) (methods.map (·.call)) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputType faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, heaps, maps, worlds, frame, metadata, next⟩ :=
    reflects_for (functions := functions) (State := Entry methods ambient.definitions caller)
      (fun invoked => invoked)
      (fun entry maps worlds frame metadata => entry.extend maps worlds frame metadata)
      (fun member entry heaps represented completed =>
        method_reflects functions extension definitions registered faithful observations runtimeViews
          uninitialized missing member entry heaps represented completed)
      chain.toFor entry heaps represented runs.toFor
  exact ⟨outcome, after, finalMap, finalWorld, SelectedTrace.ofFor trace, related, heaps, maps, worlds, frame, metadata, next⟩

variable {compilerProgram : CheckedProgram} {project : SourceCoreEvidence.Projector}
  {compilation : SourceCoreFunctions.Context} {callerFunction : SourceSpecialization.SpecializedFunction}
  {available : SourceCompilationPlan.EvidenceEnvironment} {scope : SourceCoreBasic.Scope}
  {node : ExpressionNode} {policy : SourceCoreFunctions.CallablePolicy} {ξ : Renaming}
  {inputCode outputCode : SourceCoreBasic.LoweredExpr} {calls : List CallableCoercionSpine.Call}

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- The actual emitted expression, after a successful operand, preserves the
annotated source path. The operand is outside this path-only theorem. -/
theorem emitted_preserves
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {initialStore store : Store} {input : Dynamic.Value} {native : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    {outcome : Dynamic.ExpressionOutcome} (trace : SelectedTrace methods before input outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore ∧
      PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨value, finalStore, finalMap, finalWorld, runs, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    preserves functions extension definitions registered faithful observations runtimeViews uninitialized missing chain entry heaps represented trace compilation.internalReason
  refine ⟨_, _, _, _, (emitted.spine.renamed_completed_iff ξ).mpr ?_, trace.sound, related,
    finalHeaps, maps, worlds, frame, metadata, finalEntry⟩
  exact ⟨_, _, operand, emitted.calls_eq ▸ runs⟩

include extension definitions registered faithful observations runtimeViews uninitialized missing in
/-- Completion of the actual renamed emitted code yields the independent source
path at the real dictionaries. The known operand trace fixes its reached state
by evaluation determinism; saved captures are never renamed. -/
theorem emitted_reflects
    (emitted : Emitted compilerProgram project compilation callerFunction available scope node policy ξ inputCode methods outputCode calls)
    {source target : TypeSystem.Ty} (chain : Chain source inputCode.type methods target outputCode.type)
    {caller : Environment} {mapping : LocationMap} {world : StoreTyping}
    {before : Dynamic.Heap} {initialStore store finalStore : Store} {input : Dynamic.Value} {native value : Value}
    (entry : Entry methods ambient.definitions caller mapping world before store)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (represented : ValueRep values.checked registry functions mapping world source input native inputCode.type)
    (operand : Evaluates caller initialStore (inputCode.expression.rename ξ) (.inRight .word native) store)
    (completed : Evaluates caller initialStore (outputCode.expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      SelectedTrace methods before input outcome after ∧ PathOutcome methods before input outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions) finalMap finalWorld
        target outputCode.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry methods ambient.definitions caller finalMap finalWorld after finalStore) := by
  obtain ⟨actualInput, reached, actualOperand, runs⟩ := (emitted.spine.renamed_completed_iff ξ).mp completed
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic actualOperand operand
  rw [← emitted.calls_eq] at runs
  obtain ⟨outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩ :=
    reflects functions extension definitions registered faithful observations runtimeViews uninitialized missing chain entry heaps represented runs
  exact ⟨_, _, _, _, trace, trace.sound, related, finalHeaps, maps, worlds, frame, metadata, finalEntry⟩


end Solcore.SourceSemantics.CoreLowering.CallableCoercionPathMeaning
