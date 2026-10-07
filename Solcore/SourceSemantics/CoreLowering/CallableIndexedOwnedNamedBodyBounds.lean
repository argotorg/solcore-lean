import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCanonicalState
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily

/-! A real named parameter entry supplies its original canonical globals.
The body family keeps those proofs alongside actual pools, while strict callee
callbacks receive the same concrete pools through the original low contracts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
open CallableIndexedOwnedFunctionState CallableIndexedOwnedExpressionHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {condition : BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header}

/-- The complete real parameter entry supplies globals at its own body prefix.
The wrapped initial and returned witnesses contain the exact actual pools. -/
theorem preserves_of_canonical {size : Nat}
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) condition size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (protocol headers keys) condition size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after allowed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry ⟨initial, entry.catalog.globals⟩ allowed trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

/-- Native completion returns its original independent Source grade and the
same actual reached pool after forgetting only the canonical-slot proof. -/
theorem reflects_of_canonical {size : Nat}
    (meaning : RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) condition size) :
    RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
      (protocol headers keys) condition size := by
  intro arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore allowed completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned, related⟩ :=
    meaning entry ⟨initial, entry.catalog.globals⟩ allowed completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, returned.val, related⟩

section Family
variable (runtime : Bool)
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  (sameLayouts : ∀ header, header ∈ headers → header.layouts = compiled.indexed.layouts)
  (escaped : ∀ header, header ∈ headers → faults .controlEscapedFunction header.escaped)
  (certificates : CallableIndexedOwnedFunctionValues.Header compiled program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)

def stableCondition (header : CallableIndexedOwnedFunctionValues.Header compiled program) :
    BodyCondition (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
      (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header :=
  CallableIndexedOwnedInvocationBounds.stableOwnerCondition (headers := headers) (keys := keys)
    (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header

variable (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : NativeFrame} {ghost : GhostFrame},
      (entry : BodyState (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        headers owner.key.locations owner.key.capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      stableCondition functions owner header entry →
      MatchProfileWith (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
        (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
        (certificates header) diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

private def producer {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers) :
    ProtectedStateTransition.MarkedAllocation.Producer
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
      header.layouts compiled.indexed.ancestry.layout.frame
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) :=
  (sameLayouts header member).symm ▸ CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)

private theorem ready_layout {first second : SourceCoreAllocationLayouts.Prepared}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (same : first = second)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer
      (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) second compiled.indexed.ancestry.layout.frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt ((same.symm ▸ marked).toOrdinary) location native := by
  cases same
  exact ready

private theorem acquire {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (location : Location) (native : NativeFrame)
    (stable : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producer (registry := registry) functions owner sameLayouts member).toOrdinary location native := by
  exact ready_layout owner (sameLayouts header member)
    (CallableIndexedOwnedCanonicalState.markedProducer owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions))
    (CallableIndexedOwnedCanonicalState.readyAt_of_stableOwner owner (owner.key.capturePrefix + 1)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) stable)

include extension faithful observations sameLayouts escaped profileProvider in
/-- The shared actual body fold closes callee meanings internally. Original
parameter globals authorize the canonical proof wrapper at each callee input. -/
theorem preserves_at_with_family
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
          (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
          (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry callee faults
          (protocol headers keys) (stableCondition functions owner callee))) →
      ProtectedStateTransition.PreservesAt (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
        (protocol headers keys) (stableCondition functions owner header) size := by
  have bodies := CallableRuntimeNamedBodyFamily.preserves_at
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) runtime functions extension faithful observations escaped
    (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) (stableCondition functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (registry := registry) functions owner sameLayouts member)
    (fun header member => acquire (registry := registry) functions owner sameLayouts member)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner (owner.key.capturePrefix + 1))
    (CallableIndexedOwnedCanonicalState.bindings owner (owner.key.capturePrefix + 1))
    certificates profileProvider
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact allowed)
    (by
      intro header member context valid budget child within below
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict
      exact preserves_of_canonical functions owner (below callee calleeMember smaller strict)) size
  intro header member
  exact preserves_of_canonical functions owner (bodies header member)

include extension faithful observations sameLayouts escaped profileProvider functionTypes in
/-- The shared actual body fold closes callee meanings internally. Original
parameter globals authorize the canonical proof wrapper at each callee input. -/
theorem reflects_at_with_family
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
          (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
          (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry callee faults
          (protocol headers keys) (stableCondition functions owner callee))) →
      ProtectedStateTransition.ReflectsAt (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1))
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (headers := headers)
        (locations := owner.key.locations) (capturePrefix := owner.key.capturePrefix) functions registry header faults
        (protocol headers keys) (stableCondition functions owner header) size := by
  have bodies := CallableRuntimeNamedBodyFamily.reflects_at
      (prepared := compiled.indexed.ancestry) (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) runtime functions extension faithful observations functionTypes escaped
    (argumentProtocol (headers := headers) owner (owner.key.capturePrefix + 1)) (stableCondition functions owner)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun header member => producer (registry := registry) functions owner sameLayouts member)
    (fun header member => acquire (registry := registry) functions owner sameLayouts member)
    (CallableIndexedOwnedCanonicalState.administrativeTransport owner (owner.key.capturePrefix + 1))
    (CallableIndexedOwnedCanonicalState.bindings owner (owner.key.capturePrefix + 1))
    certificates profileProvider
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry allowed
      exact allowed)
    (by
      intro header member context valid budget child within below
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict
      exact reflects_of_canonical functions owner (below callee calleeMember smaller strict)) size
  intro header member
  exact reflects_of_canonical functions owner (bodies header member)

end Family
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBodyBounds
