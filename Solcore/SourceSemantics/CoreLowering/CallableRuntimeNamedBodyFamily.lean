import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyStaticOrigins
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! The named family closes actual callee states through the shared measured
body fold. Profiles and gate receipts are obtained only at real parameter
entries; expression children receive strictly smaller actual body meanings. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds
universe u v
variable (runtime : Bool) {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditions : ∀ header, BodyCondition (headers := headers) (locations := locations)
    (capturePrefix := capturePrefix) functions registry header)
  (conditionGate : Header prepared values ambient.definitions program → Location → CallableIndexedHistory.NativeFrame → Prop)
  (producers : ∀ header, header ∈ headers → ProtectedStateTransition.MarkedAllocation.Producer protocol header.layouts
    prepared.layout.frame (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ header (member : header ∈ headers) location native, conditionGate header location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt (producers header member).toOrdinary location native)
  (stateTransport : ProtectedStateTransition.AdministrativeTransport protocol)
  (stateBindings : ProtectedStateTransition.Bindings protocol)
  (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      conditions header entry →
      MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence)
        (certificates header) diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
  (gateOf : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      conditions header entry → conditionGate header frameLocation current)

include extension faithful observations escaped producers acquire stateTransport stateBindings profileProvider gateOf in
/-- Source traces keep their original grade and exact reached pool. No body meaning is an external premise. -/
theorem preserves_at
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
          (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults protocol (conditions callee))) →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyPreservesAtWith
        (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults protocol (conditions header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named runtime index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.preserves_at origins functions extension program faithful observations
    protocol (fun index => conditionGate index.1.val) (fun index => producers index.1.val index.1.property)
    (fun index => acquire index.1.val index.1.property) stateTransport stateBindings
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after aligned trace
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate callee)
        runtime actualProfile (escaped callee calleeMember) entry initial (gateOf callee calleeMember entry aligned)
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial outcome after aligned trace
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate header)
    runtime profile (escaped header member) entry initial (gateOf header member entry aligned)
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, transition⟩

include extension faithful observations escaped producers acquire stateTransport stateBindings profileProvider gateOf functionTypes in
/-- Native completions return independent source grades and the actual body post. No body meaning is an external premise. -/
theorem reflects_at
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.solved context header.function.evidence →
      ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
          (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults protocol (conditions callee))) →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults child)
    (size : Nat) : ∀ header, header ∈ headers →
      RecursiveNamedCatalogInvocationBounds.Stateful.BodyReflectsAtWith
        (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
        functions registry header faults protocol (conditions header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => RecursiveNamedCatalogMutualMeaning.ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults := fun index =>
    CallableRuntimeBodyStaticOrigins.named runtime index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.Stateful.reflects_at origins functions extension program faithful observations functionTypes
    protocol (fun index => conditionGate index.1.val) (fun index => producers index.1.val index.1.property)
    (fun index => acquire index.1.val index.1.property) stateTransport stateBindings
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore aligned completed
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate callee)
        runtime actualProfile (escaped callee calleeMember) entry initial (gateOf callee calleeMember entry aligned)
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry initial value finalStore aligned completed
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := CallableRuntimeBodyStaticOrigins.named_entry protocol (conditionGate header)
    runtime profile (escaped header member) entry initial (gateOf header member entry aligned)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, transition⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, transition⟩

end Solcore.SourceSemantics.CoreLowering.CallableRuntimeNamedBodyFamily
