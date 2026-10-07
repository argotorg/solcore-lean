import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedInvocationBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallEvidenceHeads
import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge

/-! Actual ordered arguments hand their reached pool to the selected named
invocation. The original canonical global slot is a separate caller receipt;
the pool supplies only its actual row authority and exact full live capture.
Source and native children retain their original independent grades. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState

private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {certificate : GenericExpressionMeaning.Certificate}
  (children : DataExpressionSequence.Tree source certificate scope ids
    (header.bindings.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = header.bindings.map Prod.snd)
  (packedType : header.named.signature.parameterType = (SourceCoreCalls.packArguments codes).type)

/-- Original canonical global slots are separate from physical pool ownership.
This receipt can come from the genuine body capture or public bootstrap layout. -/
def Globals (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (callerPrefix : Nat) (scope : SourceCoreLocalCell.Scope) (canonical : Environment) : Prop :=
  ∀ header, header ∈ headers → canonical[scope.length + callerPrefix + header.slot]? =
    some (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header))

/-- A pointwise actual head contract with the original caller slot receipt.
The input State is the concrete pool; the result retains its reached Transition. -/
def PreservesAtWithGlobals
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩,
    Globals (headers := headers) owner callerPrefix scope canonical →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- Native completion keeps its independent source output grade and the actual
pool after execution; the original caller slots remain an explicit input. -/
def ReflectsAtWithGlobals
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (certificate : GenericExpressionMeaning.Certificate) (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
  ∀ initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩,
    Globals (headers := headers) owner callerPrefix scope canonical →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld node.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- A stateful noncall leaf can use the stronger caller domain without
changing its actual evaluation or post-state witness. -/
theorem PreservesAtWithGlobals.of_stateful
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial _globals trace
  exact meaning certified found environments heaps locals agrees typed initial trace

/-- Independent native/source grades and the concrete reached state pass
unchanged through this caller-domain adapter. -/
theorem ReflectsAtWithGlobals.of_stateful
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size) :
    ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial _globals completed
  exact meaning certified found environments heaps locals agrees typed initial completed

/-- The argument wrapper adds only the original canonical-slot proof. Its
records and relation are exactly those of the contained actual pool. -/
def argumentProtocol (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) :
    ProtectedStateTransition.Protocol (Records keys) where
  State := fun index => { _pool : State headers keys index //
    Globals (headers := headers) owner callerPrefix index.scope index.canonical }
  records := fun state => records state.val
  Relates := fun initial reached => Relates initial.val reached.val
  refl := fun initial => Relates.refl initial.val
  trans := fun first last => first.trans last

private theorem argument_preserves_at
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    meaning certified found environments heaps locals agrees typed initial.val initial.property trace
  obtain ⟨reached, related⟩ := transition
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨⟨reached, initial.property⟩, related⟩⟩

private theorem argument_reflects_at
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, transition⟩ :=
    meaning certified found environments heaps locals agrees typed initial.val initial.property completed
  obtain ⟨reached, related⟩ := transition
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadata, ⟨⟨reached, initial.property⟩, related⟩⟩

/-- Public bridge into the exact proof-only caller protocol used by shared
ordered arguments and higher body adapters. -/
theorem PreservesAtWithGlobals.to_stateful
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size) :
    ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size :=
  argument_preserves_at functions owner callerPrefix meaning

/-- The same exact bridge retains the independent source grade reconstructed
from the original measured native completion. -/
theorem ReflectsAtWithGlobals.to_stateful
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat) {size : Nat}
    (meaning : ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate size) :
    ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner callerPrefix)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults size :=
  argument_reflects_at functions owner callerPrefix meaning

include functions children nativeTypes packedType in
/-- The actual argument post supplies the selected live capture and the caller
pool for the real invocation. Argument failure retains its reached witness. -/
theorem call_preserves_bounded_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {callerPrefix : Nat}
    (argumentMeaning : Below budget (PreservesAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate))
    (bodyMeaning : Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) condition))
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (globals : Globals (headers := headers) owner callerPrefix scope canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {size : Nat} {reason : Word} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
      header.instantiation size outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
        ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix) child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults := by
    intro child smaller
    exact ProtectedStateTransition.SequenceBridge.preserves_at _
      (argument_preserves_at functions owner callerPrefix (argumentMeaning child smaller))
  cases trace with
  | argumentFault failed smaller =>
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentEvaluation, matched, finalHeaps,
      maps, worlds, frame, metadata, argumentTransition⟩ :=
      ProtectedDataExpressionSequence.Stateful.preserves_fault_bounded (argumentProtocol (headers := headers) owner callerPrefix) budget children argumentsMeaning
        environments heaps locals agrees typed ⟨caller, globals⟩ failed (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
    refine ⟨_, finalStore, finalMap, finalWorld, SourceCoreCalls.call_argument_failure (packedType.symm ▸ argumentEvaluation),
      (by simpa only [header.resultType] using (FunctionCalls.ResultRepresents.fault
        (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        (mapping := finalMap) (world := finalWorld) (sourceType := header.function.resultType)
        (type := header.named.signature.resultType) matched)), finalHeaps, maps, worlds, frame, metadata, ?_⟩
    obtain ⟨reached, related⟩ := argumentTransition
    exact ⟨reached.val, related⟩
  | @apply argumentsSize callSize arguments middle outcome after evaluated called argumentsSmaller callSmaller =>
    obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentEvaluation, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentTransition⟩ :=
      ProtectedDataExpressionSequence.Stateful.preserves_values_bounded (argumentProtocol (headers := headers) owner callerPrefix) budget children argumentsMeaning
        environments heaps locals agrees typed ⟨caller, globals⟩ evaluated (Nat.le_of_lt (Nat.lt_of_lt_of_le argumentsSmaller within))
    rw [nativeTypes] at represented
    have related := values_arguments header.bindings represented
    have arity : header.function.parameters.length = arguments.length := by
      rw [header.parameters, List.length_map]; exact related.length.1
    obtain ⟨bodySize, bodyTrace, bodySmaller⟩ := RecursiveNamedCallBounds.source_call_body owners header.frame arity called
    obtain ⟨middleState, argumentRelated⟩ := argumentTransition
    obtain ⟨capture⟩ := (middleState.val.rows owner.position).authority.captures header member
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluation, result, finalHeaps,
      bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
      CallableIndexedOwnedInvocationBounds.invocation_preserves_bounded_with owner sameLayouts condition authorized budget bodyMeaning
        middleState.val member capture related middleHeaps bodyTrace
        (Nat.le_of_lt (Nat.lt_trans bodySmaller (Nat.lt_of_lt_of_le callSmaller within)))
    have selected := OptionalCell.read_success reason
      (show Evaluates (DataPatternValues.packValues payloads :: actual) middleStore
        (.var (ξ (scope.length + callerPrefix + header.slot) + 1))
        (.cellRef (OptionalCell.cellType header.named.signature.functionType) (owner.key.locations header)) middleStore
        from .var (agrees (globals header member))) capture.read
    obtain ⟨finalState, bodyRelated⟩ := bodyTransition
    exact ⟨value, finalStore, finalMap, finalWorld, SourceCoreCalls.call_success argumentEvaluation selected bodyEvaluation,
      result, finalHeaps, argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
      argumentMetadata.trans bodyMetadata, ⟨finalState, argumentRelated.trans bodyRelated⟩⟩

include functions children nativeTypes packedType in
/-- The measured native call chooses its real argument and body children.
Reflection consumes their actual reached pools and preserves the independent
source grade rather than comparing it with the native input grade. -/
theorem call_reflects_bounded_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (condition : BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation condition)
    (budget : Nat)
    {callerPrefix : Nat}
    (argumentMeaning : Below budget (ReflectsAtWithGlobals (headers := headers) (registry := registry) (faults := faults)
      (source := source) (context := context) (evidence := evidence) functions owner callerPrefix certificate))
    (bodyMeaning : Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) condition))
    (member : header ∈ headers)
    {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {administrative actualContext : Core.Context} {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (globals : Globals (headers := headers) owner callerPrefix scope canonical)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world
      administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    {size : Nat} {reason : Word}
    (completed : EvaluationSize size actual store (SourceCoreCalls.call header.named.signature (ξ (scope.length + callerPrefix + header.slot))
      ((SourceCoreCalls.packArguments codes).expression.rename ξ) reason) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedArgumentTraceBounds.TraceAt program context evidence header.function.evidence source environment before ids
        header.instantiation sourceSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) caller
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have argumentsMeaning : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix) child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults := by
    intro child smaller
    exact ProtectedStateTransition.SequenceBridge.reflects_at _
      (argument_reflects_at functions owner callerPrefix (argumentMeaning child smaller))
  obtain ⟨argumentSize, argumentValue, middleStore, argumentSmaller, argumentEvaluation⟩ := RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
    argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentTransition⟩ :=
    ProtectedDataExpressionSequence.Stateful.reflects_bounded (argumentProtocol (headers := headers) owner callerPrefix) budget children argumentsMeaning
      environments heaps locals agrees typed ⟨caller, globals⟩ argumentEvaluation (Nat.lt_of_lt_of_le argumentSmaller within)
  cases represented with
  | fault matched =>
    cases argumentTrace with
    | fault failed =>
      have evaluation := SourceCoreCalls.call_argument_failure (signature := header.named.signature)
        (index := ξ (scope.length + callerPrefix + header.slot)) (internalReason := reason) (packedType.symm ▸ argumentEvaluation.sound)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluation
      refine ⟨SourceExecutionSize.stepSize [sourceSize], .fault _, middle, middleMap, middleWorld,
        .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp)),
        (by simpa only [header.resultType] using (FunctionCalls.ResultRepresents.fault
          (model := CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          (mapping := middleMap) (world := middleWorld) (sourceType := header.function.resultType)
          (type := header.named.signature.resultType) matched)),
        middleHeaps, argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, ?_⟩
      obtain ⟨reached, related⟩ := argumentTransition
      exact ⟨reached.val, related⟩
  | values represented =>
    cases argumentTrace with
    | values evaluatedArguments =>
      rw [nativeTypes] at represented
      have related := values_arguments header.bindings represented
      obtain ⟨middleState, argumentRelated⟩ := argumentTransition
      obtain ⟨capture⟩ := (middleState.val.rows owner.position).authority.captures header member
      obtain ⟨bodyNativeSize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
        argumentEvaluation.sound (agrees (globals header member)) capture.read completed
      obtain ⟨bodySourceSize, outcome, after, finalMap, finalWorld, bodyTrace, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, bodyTransition⟩ :=
        CallableIndexedOwnedInvocationBounds.invocation_reflects_bounded_with owner sameLayouts condition authorized budget bodyMeaning
          middleState.val member capture related middleHeaps bodyEvaluation
          (Nat.le_of_lt (Nat.lt_of_lt_of_le bodySmaller within))
      have called := RecursiveNamedCallBounds.call_of_body (context := context) (caller := evidence) header.frame bodyTrace
      obtain ⟨finalState, bodyRelated⟩ := bodyTransition
      exact ⟨SourceExecutionSize.stepSize [sourceSize, SourceExecutionSize.stepSize [bodySourceSize]], outcome, after, finalMap, finalWorld,
        .apply evaluatedArguments called (SourceExecutionSize.child_lt_stepSize (by simp))
          (SourceExecutionSize.child_lt_stepSize (by simp)), result, finalHeaps,
        argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds, argumentFrame.trans bodyFrame,
        argumentMetadata.trans bodyMetadata, ⟨finalState, argumentRelated.trans bodyRelated⟩⟩


variable {compilation : SourceCoreFunctions.Context}

/-- Original ordinary/direct call metadata selects the actual header and keeps
all caller/callee evidence and synthetic validation order in the source trace.
Only genuinely smaller argument and body callbacks are consumed. -/
theorem preserves_at_with
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
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    cases ordinary with
    | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
      intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
        environments heaps locals agrees typed initial globals trace
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      have independent := RecursiveNamedArgumentTraceBounds.source_inv metadata form calleeFound predicates evidenceEmpty unique trace
      obtain ⟨emitted, packed, target, selected⟩ := emission.equation
      change expression = _ at emitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, preserved, heapMetadata, transition⟩ :=
        call_preserves_bounded_with functions sequence nativeTypes packed owner (sameLayouts header member)
          (conditions header) (authorized header member) budget argumentMeaning (bodyMeaning header member) owners member
          initial globals environments heaps locals agrees typed independent within
      refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
        maps, worlds, preserved, heapMetadata, transition⟩
      · change Evaluates actual store (expression.rename ξ) value finalStore
        rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot]
        exact evaluated
      · simpa only [sourceType] using represented
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed initial globals trace
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have instantiationEq := certified.selected.metadata receipt
    have form : node.form = .call callee arguments (.declaration header.instantiation) := by
      simpa only [instantiationEq] using receipt.form
    have dictionary : Dynamic.DirectCallProducesEvidence context evidence node.requirements []
        header.instantiation.predicates header.function.evidence := by
      simpa only [metadata.coercions, instantiationEq] using certified.dictionary
    have independent := RecursiveNamedArgumentTraceBounds.source_inv_with_evidence metadata.found metadata.coercions
      form certified.calleeFound dictionary idsUnique unique trace
    have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
      simpa only [certified.selected.signature] using receipt.native.inputType
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_preserves_bounded_with functions certified.sequence certified.nativeTypes packed owner
        (sameLayouts header certified.selected.member) (conditions header) (authorized header certified.selected.member) budget
        argumentMeaning (bodyMeaning header certified.selected.member) owners certified.selected.member
        initial globals environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [certified.emitted receipt metadata.coercions]
      simpa only [NamedCalls.Arguments.call_rename] using evaluated
    · simpa only [certified.sourceType, congrArg (fun code : SourceCoreBasic.LoweredExpr => code.type)
        (certified.emitted receipt metadata.coercions)] using represented

/-- Reflection uses the original full native call completion. Reconstructed
source metadata and dictionaries stay those of the selected ordinary/direct
receipt, while the final pool is the actual invocation's reached pool. -/
theorem reflects_at_with
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
      (RecursiveNamedCallEvidenceHeads.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) size := by
  intro scope id lowered head
  cases head with
  | ordinary ordinary =>
    cases ordinary with
    | @named callee arguments header node calleeNode name codes expression member metadata sourceType form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidenceEmpty arity emission selectedSlot sequence nativeTypes =>
      intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
        environments heaps locals agrees typed initial globals evaluated
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst root
      obtain ⟨emitted, packed, target, selected⟩ := emission.equation
      change expression = _ at emitted
      change EvaluationSize size actual store (expression.rename ξ) value finalStore at evaluated
      rw [emitted, NamedCalls.Arguments.call_rename, selectedSlot] at evaluated
      obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, preserved, heapMetadata, transition⟩ :=
        call_reflects_bounded_with functions sequence nativeTypes packed owner (sameLayouts header member)
          (conditions header) (authorized header member) budget argumentMeaning (bodyMeaning header member) member
          initial globals environments heaps locals agrees typed evaluated within
      obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro metadata form calleeFound calleeForm
        calleeRequirements calleeCoercions valid predicates evidenceEmpty trace
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent, by simpa only [sourceType] using represented,
        finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩
  | @direct compilerProgram project caller child fuel id callee arguments instantiation reasonAt policy node output header receipt certified metadata =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed initial globals evaluated
    have same := Option.some.inj (metadata.found.symm.trans found)
    subst root
    have emitted := certified.emitted receipt metadata.coercions
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted] at evaluated
    simp only [NamedCalls.Arguments.call_rename] at evaluated
    have packed : header.named.signature.parameterType = (SourceCoreCalls.packArguments receipt.loweredArguments).type := by
      simpa only [certified.selected.signature] using receipt.native.inputType
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_reflects_bounded_with functions certified.sequence certified.nativeTypes packed owner
        (sameLayouts header certified.selected.member) (conditions header) (authorized header certified.selected.member) budget
        argumentMeaning (bodyMeaning header certified.selected.member) certified.selected.member
        initial globals environments heaps locals agrees typed evaluated within
    have instantiationEq := certified.selected.metadata receipt
    have form : node.form = .call callee arguments (.declaration header.instantiation) := by
      simpa only [instantiationEq] using receipt.form
    have dictionary : Dynamic.DirectCallProducesEvidence context evidence node.requirements []
        header.instantiation.predicates header.function.evidence := by
      simpa only [metadata.coercions, instantiationEq] using certified.dictionary
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro_with_evidence metadata.found
      metadata.coercions form certified.calleeFound certified.calleeForm certified.calleeRequirements certified.calleeCoercions
      certified.valid dictionary trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [certified.sourceType, congrArg (fun code : SourceCoreBasic.LoweredExpr => code.type) emitted] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
