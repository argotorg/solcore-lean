import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds

/-! Strong induction closes the finite catalog's body obligations. Static
profiles retain actual compiler equations at each reachable body entry;
they require no profiles for arbitrary unreachable contexts and contain no execution law. Source and native sizes use separate inductions.
An actual call selects a strictly smaller body; structural expression children
may have the same size. Initial catalog authority remains an independent input
to the resulting invocation contracts. Whole compiler extraction and arbitrary
qualified/lambda expressions remain separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogInvocationBounds

section Match

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      MatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_match (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
    let profile := profiles header member entry
    have children : ∀ context, CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence →
        RecursiveNamedHeaderContracts.AtMost size (fun child => RecursiveNamedBoundedContracts.PreservesAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (Expressions headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (capturePrefix + 1))) := by
      intro context valid child within
      have meaning : RecursiveNamedBoundedContracts.PreservesAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (Expressions headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) :=
        RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
        header.function.evidence valid header.unique owners (uninitialized header member) (missing header member)
        size child within (fun callee calleeMember smaller strict => ih smaller strict callee calleeMember)
      rw [prefixMatches header member] at meaning
      exact @meaning
    have flow : RecursiveNamedLoopContracts.PreservesAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        size (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow :=
      RecursiveNamedImperativeFor.preservesAt_match functions header.definitions_eq header.registered extension
        program header.function.evidence entry_transport entry_binds size faithful observations children diagnosticPolicy header.unique
        profile.tree profile.errors size (Nat.le_refl size)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
      RecursiveNamedCatalogBodyFinishBounds.state_preserves_at_match functions (escaped header member) profile size flow entry trace
    exact ⟨value, finalStore, finalMap, finalWorld, evaluation, result, heaps, maps, worlds, frame, metadata⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_match (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  induction size using Nat.strongRecOn with
  | ind size ih =>
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
    let profile := profiles header member entry
    have children : ∀ context, CompatibleExpressionLiterals.ContextValid header.solved context header.function.evidence →
        RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedBoundedContracts.ReflectsAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (Expressions headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (capturePrefix + 1))) := by
      intro context valid child smaller
      have meaning : RecursiveNamedBoundedContracts.ReflectsAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (Expressions headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) :=
        RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
        header.function.evidence valid (uninitialized header member) (missing header member)
        size child (Nat.le_of_lt smaller) (fun callee calleeMember smaller strict => ih smaller strict callee calleeMember)
      rw [prefixMatches header member] at meaning
      exact @meaning
    have flow : RecursiveNamedBoundedContracts.Below size (fun child => RecursiveNamedLoopContracts.ReflectsAt
        (entry := protectedEntry headers locations capturePrefix (capturePrefix + 1)) functions program header.function.evidence
        (source := header.function.source) (context := header.context) (registry := registry) (solved := header.solved) (faults := faults)
        (frameLayout := prepared.layout.frame) (globals := header.globals)
        (administrative := SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative)
        child (scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
        true header.function.body header.function.resultType header.output profile.flow) :=
      RecursiveNamedImperativeFor.reflectsAt_match functions header.definitions_eq header.registered extension
        program header.function.evidence entry_transport entry_binds size children faithful observations diagnosticPolicy runtimeViews header.unique
        profile.tree profile.errors
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
      RecursiveNamedCatalogBodyFinishBounds.state_reflects_at_match functions (escaped header member) profile size size (Nat.le_refl size) flow entry completed
    exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata⟩

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_match (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
    evidence valid sourceUnique owners callerUninitialized callerMissing size size (Nat.le_refl size)
    (fun header member child _ => preserves_at_match functions extension faithful observations runtimeViews owners
      uninitialized missing escaped prefixMatches profiles child header member)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_match (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
    evidence valid callerUninitialized callerMissing size size (Nat.le_refl size)
    (fun header member child _ => reflects_at_match functions extension faithful observations runtimeViews
      uninitialized missing escaped prefixMatches profiles child header member)


end Match

section Legacy
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
  {compilation : Header prepared values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header prepared values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = capturePrefix + 1)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      ProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
theorem preserves_at (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_match functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
theorem reflects_at (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_match functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) size

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
theorem expression_preserves_at (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_match functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) evidence valid sourceUnique callerUninitialized callerMissing size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
theorem expression_reflects_at (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_match functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches
    (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).to_match) evidence valid callerUninitialized callerMissing size

end Legacy

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
