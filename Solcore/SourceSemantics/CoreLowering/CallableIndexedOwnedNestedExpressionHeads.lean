import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedCallerProtocol

/-! Original view and nested literal receipts consume the actual stronger
formation protocol. Ordered argument children carry the same packet into the
real named call; genuine literal formation retains the reached own history. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedNestedCanonicalState
open CallableIndexedOwnedNestedCallerProtocol (carrier)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {compilation : SourceCoreFunctions.Context}

theorem view_preserves_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (prefixMatches : compilation.administrativePrefix = 1)
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
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) program context evidence source
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  have bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) := by
    simpa only [prefixMatches] using carrier (headers := headers) owner caller
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.preserves_at_with_caller functions owner sameLayouts conditions authorized bridge
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees typed initial trace
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    have independent := RecursiveNamedArgumentTraceBounds.source_inv receipt.metadata receipt.form receipt.calleeFound
      receipt.predicates receipt.evidenceEmpty unique trace
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_preserves_bounded_with_caller functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget bridge argumentMeaning (bodyMeaning receipt.header receipt.member) owners receipt.member
        initial environments heaps locals agrees typed independent within
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩
    · change Evaluates actual store (lowered.expression.rename ξ) value finalStore
      rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot]
      exact evaluated
    · simpa only [receipt.sourceType, receipt.nativeType] using represented

theorem view_reflects_at_with
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
    (prefixMatches : compilation.administrativePrefix = 1)
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      functions registry header faults (protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) program context evidence source
      (CallableLambdaViewNamedRuntimeCertificates.Head (prepared := compiled.indexed.ancestry)
        (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers compilation source context evidence certificate) faults size := by
  have bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
      (fun index => Globals (headers := headers) owner compilation.administrativePrefix index.scope index.canonical)
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller) := by
    simpa only [prefixMatches] using carrier (headers := headers) owner caller
  intro scope id lowered head
  cases head with
  | authenticated receipt =>
    exact CallableIndexedOwnedExpressionHeads.reflects_at_with_caller functions owner sameLayouts conditions authorized bridge
      budget size within argumentMeaning bodyMeaning receipt
  | ordinary receipt =>
    intro root found mapping world administrative environment canonical actual actualContext before store ξ value finalStore
      environments heaps locals agrees typed initial evaluated
    have same := Option.some.inj (receipt.metadata.found.symm.trans found)
    subst root
    obtain ⟨emitted, packed, _, _⟩ := receipt.emission.equation
    change EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore at evaluated
    rw [emitted, NamedCalls.Arguments.call_rename, receipt.selectedSlot] at evaluated
    obtain ⟨traceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preserved, heapMetadata, transition⟩ :=
      call_reflects_bounded_with_caller functions receipt.sequence receipt.nativeTypes packed owner
        (sameLayouts receipt.header receipt.member) (conditions receipt.header) (authorized receipt.header receipt.member)
        budget bridge argumentMeaning (bodyMeaning receipt.header receipt.member) receipt.member
        initial environments heaps locals agrees typed evaluated within
    obtain ⟨sourceSize, independent⟩ := RecursiveNamedArgumentTraceBounds.source_intro receipt.metadata receipt.form receipt.calleeFound
      receipt.calleeForm receipt.calleeRequirements receipt.calleeCoercions receipt.valid receipt.predicates receipt.evidenceEmpty trace
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, independent,
      by simpa only [receipt.sourceType, receipt.nativeType] using represented,
      finalHeaps, maps, worlds, preserved, heapMetadata, transition⟩

section Nested
open CallableIndexedLambdaNestedRuntimeBodyMeaning
variable (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : CallableIndexedOwnedFunctionValues.Header compiled program)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)
  {rank : Nat}
local notation "F" => CallableIndexedOwnedFunctionValues.model headers keys registry faults profile
local notation "P" => CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner caller
local notation "Calls" => CallableIndexedLambdaNestedRuntimeCertificates.Head
  (LowerSupport (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) headers caller registry faults rank)
  rank caller headers (CallableIndexedNamedGeneration.context compiled.indexed caller.named) source context evidence

include prefixZero complete globals slots sameSource in
/-- The original two nested head constructors supply either the actual named
view call or genuine strong lambda formation. Their children keep this input
protocol, so original formation observations remain available after calls. -/
theorem nested_preserves_at_with
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (idsUnique : RequirementIdsUnique context) (unique : NodeOccurrencesUnique source)
    (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      F registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.PreservesAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source (Calls certificate) faults size := by
  intro scope id lowered head
  cases head with
  | existing receipt =>
    exact view_preserves_at_with F owner caller rfl sameLayouts conditions authorized
      budget size within idsUnique unique owners argumentMeaning bodyMeaning receipt
  | lambda leaf =>
    exact formation_preserves_at owner caller prefixZero profile complete globals slots sameSource size unique ⟨leaf⟩

include prefixZero complete globals slots sameSource in
/-- Native completion selects the same authentic head receipt and actual
reached protocol witness; its reconstructed Source grade stays independent. -/
theorem nested_reflects_at_with
    (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
    (conditions : ∀ header, BodyCondition (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header)
    (authorized : ∀ header, header ∈ headers → CallableIndexedOwnedInvocationBounds.BodyAuthorizationAt (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) F registry header owner.key.frameLocation (conditions header))
    (budget size : Nat) (within : size ≤ budget)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source certificate faults))
    (bodyMeaning : ∀ header, header ∈ headers → Below budget (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      F registry header faults (CallableIndexedOwnedFunctionState.protocol headers keys) (conditions header))) :
    ProtectedStateTransition.ReflectsAt P
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry F)
      program context evidence source (Calls certificate) faults size := by
  intro scope id lowered head
  cases head with
  | existing receipt =>
    exact view_reflects_at_with F owner caller rfl sameLayouts conditions authorized
      budget size within argumentMeaning bodyMeaning receipt
  | lambda leaf =>
    exact formation_reflects_at owner caller prefixZero profile complete globals slots sameSource size ⟨leaf⟩

end Nested

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionHeads
