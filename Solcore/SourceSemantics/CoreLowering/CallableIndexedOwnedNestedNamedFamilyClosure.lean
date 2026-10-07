import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! Each authentic named header has its own formation packet beside the same
actual pool. The existing measured mutual body fold closes smaller calls, and
the original nested expression Tree closes its compositional children. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (prefixZero : owner.key.capturePrefix = 0)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
variable
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) identities)
  (functionTypes : FunctionRuntimeViews (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (ranks : CallableIndexedOwnedFunctionValues.Header compiled program → Nat)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}

/-- Original static nested certificates retain the full Source and dictionary
of each named header and its genuine compiler context. -/
abbrev certificates (header : CallableIndexedOwnedFunctionValues.Header compiled program)
    (context : SourceSemantics.Context) : GenericExpressionMeaning.Certificate :=
  CallableIndexedLambdaNestedRuntimeCertificates.Certificates
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) (program := program)
    (CallableIndexedLambdaNestedRuntimeBodyMeaning.LowerSupport
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      headers header registry faults (ranks header))
    (ranks header) header headers (CallableIndexedNamedGeneration.context compiled.indexed header.named)
    header.readFuel header.function.source context header.function.evidence header.solved header.reasonAt


variable (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location} {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
        (certificates (headers := headers) (registry := registry) (faults := faults) ranks header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

private def producer {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers) :
    ProtectedStateTransition.MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) :=
  (sameLayouts header member).symm ▸ CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))

private theorem ready_layout {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    {first second : SourceCoreAllocationLayouts.Prepared}
    (same : first = second)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header) second compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      (producer (headers := headers) (registry := registry) (faults := faults) owner profile sameLayouts member).toOrdinary location native := by
  exact ready_layout owner profile (sameLayouts header member)
    (CallableIndexedOwnedNestedCanonicalState.markedProducer owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)))
    (CallableIndexedOwnedNestedCanonicalState.readyAt_of_stableOwner owner header
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)) stable)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- Source traces keep their original grades and the actual reached per-header
formation packet. Strict callees come only from the shared measured fold. -/
theorem preserves_nested_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.val.solved context header.val.function.evidence)
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header.val)
      diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named true index.2.2 (escaped index.1.val index.1.property)
  let protocols := fun index : Index => (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.1.val)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.Family.preserves_at origins
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension program faithful observations
    protocols (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun index => producer owner profile sameLayouts index.1.property)
    (fun index => acquire owner profile sameLayouts index.1.property)
    (fun index => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner index.1.val)
    (fun index => CallableIndexedOwnedNestedCanonicalState.bindings owner index.1.val)
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, bodyProfile⟩
      apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
        owner header prefixZero profile complete (globals header member) slots
        header.agreement.source extension faithful observations functionTypes header.function.evidence
        header.unique owners (uninitialized header member) (missing header member)
        sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        valid.ledger valid.runtime budget child within
      intro callee calleeMember smaller strict
      apply CallableIndexedOwnedNamedCanonicalEntries.preserves_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee
        prefixZero (globals callee calleeMember) smaller
      intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
        entry initial outcome after aligned trace
      let actualProfile := profiles callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner callee)
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
        (escaped callee calleeMember) entry initial
        (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee entry aligned)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial outcome after aligned trace
  let actualProfile := profiles header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, actualProfile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
    (escaped header member) entry initial
    (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header entry aligned)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- Native completions return their original grades and the actual reached per-header
formation packet. Strict callees come only from the shared measured fold. -/
theorem reflects_nested_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor true header.val.solved context header.val.function.evidence)
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header.val)
      diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named true index.2.2 (escaped index.1.val index.1.property)
  let protocols := fun index : Index => (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner index.1.val)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.Family.reflects_at origins
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) extension program faithful observations functionTypes
    protocols (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun index => producer owner profile sameLayouts index.1.property)
    (fun index => acquire owner profile sameLayouts index.1.property)
    (fun index => CallableIndexedOwnedNestedCanonicalState.administrativeTransport owner index.1.val)
    (fun index => CallableIndexedOwnedNestedCanonicalState.bindings owner index.1.val)
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, bodyProfile⟩
      apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
        owner header prefixZero profile complete (globals header member) slots
        header.agreement.source extension faithful observations functionTypes header.function.evidence
        (uninitialized header member) (missing header member)
        sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
        valid.ledger valid.runtime budget child within
      intro callee calleeMember smaller strict
      apply CallableIndexedOwnedNamedCanonicalEntries.reflects_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee
        prefixZero (globals callee calleeMember) smaller
      intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
        entry initial value finalStore aligned completed
      let actualProfile := profiles callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner callee)
        (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
        (escaped callee calleeMember) entry initial
        (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner callee entry aligned)
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost
    entry initial value finalStore aligned completed
  let actualProfile := profiles header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, actualProfile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry
        (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
    (CallableIndexedOwnedAllocationProducer.StableOwner keys) true actualProfile
    (escaped header member) entry initial
    (CallableIndexedOwnedNamedCanonicalEntries.stable_owner (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header entry aligned)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- Genuine parameter observations wrap the input; forgetting the final packet
returns the exact reached base pool from the internally closed family. -/
theorem preserves_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  intro header member
  exact CallableIndexedOwnedNamedCanonicalEntries.preserves_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header
    prefixZero (globals header member) size
    (preserves_nested_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
      owners uninitialized missing escaped ranks profiles size header member)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- Genuine parameter observations wrap the input; forgetting the final packet
returns the exact reached base pool from the internally closed family. -/
theorem reflects_at (size : Nat) : ∀ header, header ∈ headers →
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (headers := headers) (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) registry header faults (protocol headers keys)
      (CallableIndexedOwnedNamedCanonicalEntries.condition (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header) size := by
  intro header member
  exact CallableIndexedOwnedNamedCanonicalEntries.reflects_of_nested (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner header
    prefixZero (globals header member) size
    (reflects_nested_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
      uninitialized missing escaped ranks profiles size header member)

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  owners uninitialized missing escaped profiles in
/-- The original nested Tree closes all expression children and uses only the
strictly smaller bodies already closed by the same mutual family. -/
theorem expression_preserves_at
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (member : header ∈ headers)
    (context : SourceSemantics.Context)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
    (size : Nat) :
    ProtectedStateTransition.PreservesAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context header.function.evidence header.function.source
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header context) faults size := by
  apply CallableIndexedOwnedNestedExpressionTreeBounds.preserves_at_runtime
    owner header prefixZero profile complete (globals header member) slots
    header.agreement.source extension faithful observations functionTypes header.function.evidence
    header.unique owners (uninitialized header member) (missing header member)
    sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    valid.ledger valid.runtime size size (Nat.le_refl _)
  intro callee calleeMember child _strict
  exact preserves_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    owners uninitialized missing escaped ranks profiles child callee calleeMember

include prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
  uninitialized missing escaped profiles in
/-- The original nested Tree closes all expression children and uses only the
strictly smaller bodies already closed by the same mutual family. -/
theorem expression_reflects_at
    (header : CallableIndexedOwnedFunctionValues.Header compiled program) (member : header ∈ headers)
    (context : SourceSemantics.Context)
    (valid : RecursiveNamedCatalogMutualMeaning.ContextFor true header.solved context header.function.evidence)
    (size : Nat) :
    ProtectedStateTransition.ReflectsAt
      (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner header)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context header.function.evidence header.function.source
      (certificates (headers := headers) (registry := registry) (faults := faults) ranks header context) faults size := by
  apply CallableIndexedOwnedNestedExpressionTreeBounds.reflects_at_runtime
    owner header prefixZero profile complete (globals header member) slots
    header.agreement.source extension faithful observations functionTypes header.function.evidence
    (uninitialized header member) (missing header member)
    sameLayouts (fun target => CallableIndexedOwnedNamedCanonicalEntries.condition
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    (fun target _ => CallableIndexedOwnedNamedCanonicalEntries.authorized
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) owner target)
    valid.ledger valid.runtime size size (Nat.le_refl _)
  intro callee calleeMember child _strict
  exact reflects_at owner prefixZero profile complete globals slots sameLayouts extension faithful observations functionTypes
    uninitialized missing escaped ranks profiles child callee calleeMember

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNestedNamedFamilyClosure
