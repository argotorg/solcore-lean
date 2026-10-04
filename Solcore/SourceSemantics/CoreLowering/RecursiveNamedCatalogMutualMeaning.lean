import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogBodyFinishBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeForReflection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionTreeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogRuntimeMatchProfiles
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLambdaFormationTreeMeaning

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


/-- Selects the static context condition, without changing runtime code. -/
def ContextFor (runtime : Bool) (solved : List SolvedRequirement)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) : Prop :=
  match runtime with
  | false => CompatibleExpressionLiterals.ContextValid solved context evidence
  | true => CompatibleRuntimeContextValidity.Valid solved context evidence

theorem context_extend {runtime : Bool} {solved : List SolvedRequirement}
    {context next : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (valid : ContextFor runtime solved context evidence)
    (extended : BinderExtends owner context binder next) : ContextFor runtime solved next evidence := by
  cases runtime with
  | false => exact TypedLexicalControl.valid_extend valid extended
  | true => exact valid.extend extended

theorem context_runtime {runtime : Bool} {solved : List SolvedRequirement}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    (valid : ContextFor runtime solved context evidence) :
    CompatibleRuntimeContextValidity.Valid solved context evidence := by
  cases runtime with
  | false => exact CompatibleRuntimeContextValidity.of_ordinary valid
  | true => exact valid

section Families
variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}

/-- The ordinary tree and the same tree with actual numeric receipts are kept
as separate static cases. No ordinary receipt is cast to a selected receipt. -/
abbrev ExpressionsFor (runtime : Bool) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  match runtime with
  | false => Expressions headers compilation fuel source context solved reasonAt
  | true => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers compilation fuel source context solved reasonAt

abbrev MatchProfileForMode (runtime : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program) (compilation : SourceCoreFunctions.Context)
    (fuel : Nat) (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
    (fun context => ExpressionsFor runtime headers compilation fuel header.function.source context header.solved header.reasonAt)
    diagnosticPolicy header expressionSyntax administrative registry faults
/-- The ordinary tree and the same tree with actual numeric receipts are kept
as separate static cases. No ordinary receipt is cast to a selected receipt. -/
abbrev ExpressionsForWith (authenticated runtime : Bool) (evidence : Dynamic.EvidenceEnvironment) (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (fuel : Nat) (source : TypedSource)
    (context : SourceSemantics.Context) (solved : List SolvedRequirement) (reasonAt : ExpressionId → Word) :=
  match runtime with
  | false => Expressions headers compilation fuel source context solved reasonAt
  | true => RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (if authenticated then some evidence else none) headers compilation fuel source context solved reasonAt

abbrev MatchProfileForModeWith (authenticated runtime : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program) (compilation : SourceCoreFunctions.Context)
    (fuel : Nat) (expressionSyntax : ExpressionId → Prop) (administrative : Core.Context)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) :=
  MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
    (fun context => ExpressionsForWith authenticated runtime header.function.evidence headers compilation fuel header.function.source context header.solved header.reasonAt)
    diagnosticPolicy header expressionSyntax administrative registry faults
end Families

/-- A stronger body entry is required only at the actual parameter result.
An arbitrary BodyState remains unchanged and cannot construct this condition. -/
def BodyEntryCondition {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
    {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
    {headers : Inventory prepared values ambient.definitions program} {locations : Locations} {capturePrefix : Nat}
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (header : Header prepared values ambient.definitions program) :
    BodyCondition (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} entry =>
    P header (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      entry.mapping entry.world entry.heap entry.store entry.canonical

section EvidenceCommon

variable (authenticated runtime : Bool) {checked : Checked} {base : Base checked}
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
      MatchProfileForModeWith authenticated runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

namespace NamedFamily

/-- The real named profile supplies the neutral kernel fields directly. -/
def origin (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (binders : ProtectedExpressionMeaning.Binds P)
    {header : Header prepared values ambient.definitions program}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    (profile : MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax administrative registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped) :
    CallableRuntimeBodyOrigins.Origin values ambient registry faults :=
  { layouts := header.layouts, owner := header.owner, active := header.active
    frameLayout := prepared.layout.frame, globals := header.globals, onError := header.onError
    function := header.function, expressionSyntax := expressionSyntax, certificates := certificates
    validity := fun context => ContextFor runtime header.solved context header.function.evidence
    diagnosticPolicy := diagnosticPolicy, administrative := administrative, context := header.context
    scope := header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))
    output := header.output, code := header.body, fellThrough := header.fellThrough, escaped := header.escaped
    solved := header.solved, protectedEntry := P
    body := { flow := profile.flow, tree := profile.tree, sites := profile.errors, initialValid := profile.initialValid
              projection := profile.projection, unique := header.unique, emitted := profile.emitted }
    definitions := header.definitions_eq, registered := header.registered, escapedFault := escapedFault
    transport := transport, binders := binders, extend := fun valid extended => context_extend valid extended
    runtimeOf := fun valid => context_runtime valid }

/-- The actual parameter result supplies the full state, including its physical
frame reference. No authority is recovered from a native type. -/
def entry (P : ProtectedExpressionMeaning.Entry)
    (transport : ProtectedExpressionMeaning.Transport P) (binders : ProtectedExpressionMeaning.Binds P)
    {header : Header prepared values ambient.definitions program}
    {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
    {expressionSyntax : ExpressionId → Prop}
    {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
    {actual : Environment} {ξ : Renaming} {frameLocation : Location}
    {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
    (profile : MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence)
      certificates diagnosticPolicy header expressionSyntax
      (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (escapedFault : faults .controlEscapedFunction header.escaped)
    (state : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
      administrative actualContext actual ξ frameLocation current ghost)
    (aligned : P (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)))
      state.mapping state.world state.heap state.store state.canonical) :
    CallableRuntimeBodyOrigins.Entry (origin runtime P transport binders profile escapedFault) functions :=
  { mapping := state.mapping, world := state.world, environment := state.environment
    canonical := state.canonical, actual := state.actualBody, heap := state.heap, store := state.store
    embedding := state.embedding, actualContext := CallableIndexedParameterTyped.prefixContext header.bindings actualContext
    frameLocation := frameLocation, native := current
    environments := state.environments, heaps := state.heaps, locals := state.locals, lookups := state.lookups
    actualTyped := state.actualTyped, reference := by simpa only [origin, List.length_map, List.length_reverse] using state.reference
    read := state.state.read
    unmapped := Eq.mp (congrArg (fun location => location ∉ state.mapping) state.catalog_frame) state.catalog.authority.unmapped
    installed := aligned }

end NamedFamily

include extension faithful observations escaped in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with_family
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (transports : ∀ header, ProtectedExpressionMeaning.Transport (P header))
    (binders : ∀ header, ProtectedExpressionMeaning.Binds (P header))
    (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      BodyEntryCondition functions registry P header entry →
      MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence) (certificates header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      ContextFor runtime header.solved context header.function.evidence → ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (BodyPreservesAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults (BodyEntryCondition functions registry P callee))) →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults (P header))
    (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAtWith
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (BodyEntryCondition functions registry P header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.Origin values ambient registry faults := fun index =>
    NamedFamily.origin runtime (P index.1.val) (transports index.1.val) (binders index.1.val) index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.preserves_at origins functions extension program faithful observations
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after aligned trace
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := NamedFamily.entry runtime functions (P callee) (transports callee) (binders callee)
        actualProfile (escaped callee calleeMember) entry aligned
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
        meaning actualEntry trace
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after aligned trace
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := NamedFamily.entry runtime functions (P header) (transports header) (binders header)
    profile (escaped header member) entry aligned
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    bodies index actualEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds, frame, metadata⟩

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  have bodies := preserves_at_with_family runtime functions extension faithful observations escaped
    (fun _ => protectedEntry headers locations capturePrefix (capturePrefix + 1))
    (fun _ => entry_transport) (fun _ => entry_binds)
    (fun header context => ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact profiles header member entry)
    (by
      intro header member context valid budget child within below
      have oldBodies : ∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
          (BodyPreservesAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry callee faults) := by
        intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
        exact below callee calleeMember smaller strict entry ⟨entry.catalog⟩ trace
      have meaning : RecursiveNamedBoundedContracts.PreservesAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) := by
        cases runtime with
        | false =>
          exact RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
            header.function.evidence valid header.unique owners (uninitialized header member) (missing header member) budget child within oldBodies
        | true =>
          exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime_with functions extension faithful observations runtimeViews
            header.function.evidence header.unique owners (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within oldBodies
      rw [prefixMatches header member] at meaning
      exact @meaning) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry outcome after trace
  exact bodies header member entry ⟨entry.catalog⟩ trace

include extension faithful observations runtimeViews escaped in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with_family
    (P : Header prepared values ambient.definitions program → ProtectedExpressionMeaning.Entry)
    (transports : ∀ header, ProtectedExpressionMeaning.Transport (P header))
    (binders : ∀ header, ProtectedExpressionMeaning.Binds (P header))
    (certificates : Header prepared values ambient.definitions program → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
  (profileProvider : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState headers locations capturePrefix functions registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost) →
      BodyEntryCondition functions registry P header entry →
      MatchProfileWith (fun context => ContextFor runtime header.solved context header.function.evidence) (certificates header)
        diagnosticPolicy header (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)
    (expressionMeaning : ∀ header, header ∈ headers → ∀ context,
      ContextFor runtime header.solved context header.function.evidence → ∀ budget child, child ≤ budget →
      (∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
        (BodyReflectsAtWith (headers := headers) (locations := locations) (capturePrefix := capturePrefix)
          functions registry callee faults (BodyEntryCondition functions registry P callee))) →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context header.function.evidence header.function.source (certificates header context) faults (P header))
    (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAtWith
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults (BodyEntryCondition functions registry P header) size := by
  let Index := Σ header : {header // header ∈ headers}, Σ administrative : Core.Context,
    MatchProfileWith (fun context => ContextFor runtime header.val.solved context header.val.function.evidence)
      (certificates header.val) diagnosticPolicy header.val (expressionSyntax header.val)
      (SourceCoreCompatibleCatalog.packTypes (header.val.bindings.map Prod.snd) :: administrative) registry faults
  let origins : Index → CallableRuntimeBodyOrigins.Origin values ambient registry faults := fun index =>
    NamedFamily.origin runtime (P index.1.val) (transports index.1.val) (binders index.1.val) index.2.2 (escaped index.1.val index.1.property)
  have bodies := CallableRuntimeBodyMutualMeaning.reflects_at origins functions extension program faithful observations runtimeViews
    (by
      intro index context valid budget child within below
      rcases index with ⟨⟨header, member⟩, administrative, profile⟩
      apply expressionMeaning header member context valid budget child within
      intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore aligned completed
      let actualProfile := profileProvider callee calleeMember entry aligned
      let target : Index := ⟨⟨callee, calleeMember⟩, administrative, actualProfile⟩
      have meaning := below target smaller strict
      let actualEntry := NamedFamily.entry runtime functions (P callee) (transports callee) (binders callee)
        actualProfile (escaped callee calleeMember) entry aligned
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
        meaning actualEntry completed
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata⟩) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore aligned completed
  let profile := profileProvider header member entry aligned
  let index : Index := ⟨⟨header, member⟩, administrative, profile⟩
  let actualEntry := NamedFamily.entry runtime functions (P header) (transports header) (binders header)
    profile (escaped header member) entry aligned
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata, _, _⟩ :=
    bodies index actualEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds, frame, metadata⟩

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  have bodies := reflects_at_with_family runtime functions extension faithful observations runtimeViews escaped
    (fun _ => protectedEntry headers locations capturePrefix (capturePrefix + 1))
    (fun _ => entry_transport) (fun _ => entry_binds)
    (fun header context => ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt)
    (by
      intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry aligned
      exact profiles header member entry)
    (by
      intro header member context valid budget child within below
      have oldBodies : ∀ callee, callee ∈ headers → RecursiveNamedBoundedContracts.Below budget
          (BodyReflectsAt (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry callee faults) := by
        intro callee calleeMember smaller strict arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
        exact below callee calleeMember smaller strict entry ⟨entry.catalog⟩ completed
      have meaning : RecursiveNamedBoundedContracts.ReflectsAt child
          (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context header.function.evidence header.function.source
          (ExpressionsForWith authenticated runtime header.function.evidence headers (compilation header) header.readFuel header.function.source context header.solved header.reasonAt) faults
          (protectedEntry headers locations capturePrefix (compilation header).administrativePrefix) := by
        cases runtime with
        | false =>
          exact RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
            header.function.evidence valid (uninitialized header member) (missing header member) budget child within oldBodies
        | true =>
          exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime_with functions extension faithful observations runtimeViews
            header.function.evidence (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within oldBodies
      rw [prefixMatches header member] at meaning
      exact @meaning) size
  intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry value finalStore completed
  exact bodies header member entry ⟨entry.catalog⟩ completed

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_with_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsForWith authenticated runtime evidence headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  cases runtime with
  | false =>
    exact RecursiveNamedExpressionTreeBounds.preserves_at functions extension faithful observations runtimeViews
      evidence valid sourceUnique owners callerUninitialized callerMissing size size (Nat.le_refl size)
      (fun header member child _ => preserves_at_with_evidence authenticated false functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles child header member)
  | true =>
    exact RecursiveNamedExpressionTreeBounds.preserves_at_runtime_with functions extension faithful observations runtimeViews
      evidence sourceUnique owners callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl size)
      (fun header member child _ => preserves_at_with_evidence authenticated true functions extension faithful observations runtimeViews owners
        uninitialized missing escaped prefixMatches profiles child header member)

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_with_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsForWith authenticated runtime evidence headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  cases runtime with
  | false =>
    exact RecursiveNamedExpressionTreeBounds.reflects_at functions extension faithful observations runtimeViews
      evidence valid callerUninitialized callerMissing size size (Nat.le_refl size)
      (fun header member child _ => reflects_at_with_evidence authenticated false functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)
  | true =>
    exact RecursiveNamedExpressionTreeBounds.reflects_at_runtime_with functions extension faithful observations runtimeViews
      evidence callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl size)
      (fun header member child _ => reflects_at_with_evidence authenticated true functions extension faithful observations runtimeViews
        uninitialized missing escaped prefixMatches profiles child header member)


end EvidenceCommon

section Common

variable (runtime : Bool) {checked : Checked} {base : Base checked}
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
      MatchProfileForMode runtime diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_with (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_with (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles size

variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : ContextFor runtime solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_with (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsFor runtime headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with_evidence false runtime functions extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_with (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (ExpressionsFor runtime headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with_evidence false runtime functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end Common

section Ordinary

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
  exact preserves_at_with false functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_match (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with false functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) size


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
  exact expression_preserves_at_with false functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_match (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (Expressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with false functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches (fun header member {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} {_} entry =>
      (profiles header member entry).toMatchProfileWith) evidence valid callerUninitialized callerMissing size


end Ordinary

section Runtime

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
      RuntimeMatchProfileFor diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_runtime (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_runtime (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles size


variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_runtime (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_runtime (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressions headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end Runtime

section RuntimeEvidence

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
      RuntimeMatchProfileForWith true diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults)

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles in
/-- No callee/body execution meaning is an external premise. The original
source body grade determines the strong-induction budget. -/
theorem preserves_at_runtime_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact preserves_at_with_evidence true true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles in
/-- Completed native bodies select only original strict native children.
Reflection constructs independent source grades; preservation is not an input. -/
theorem reflects_at_runtime_evidence (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAt
      (headers := headers) (locations := locations) (capturePrefix := capturePrefix) functions registry header faults size := by
  exact reflects_at_with_evidence true true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles size


variable {callerCompilation : SourceCoreFunctions.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {fuel : Nat}
  (evidence : Dynamic.EvidenceEnvironment)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (sourceUnique : NodeOccurrencesUnique source)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include extension faithful observations runtimeViews owners uninitialized missing escaped prefixMatches profiles valid sourceUnique callerUninitialized callerMissing in
/-- The same structural expression family can now call every catalog body,
including itself and mutual targets, without an external body meaning law. -/
theorem expression_preserves_at_runtime_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (some evidence) headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_preserves_at_with_evidence true true functions extension faithful observations runtimeViews owners
    uninitialized missing escaped prefixMatches profiles evidence valid sourceUnique callerUninitialized callerMissing size


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches profiles valid callerUninitialized callerMissing in
/-- Native expression completion reflects through the closed catalog. Its
source grade is produced independently by the reflected child derivations. -/
theorem expression_reflects_at_runtime_evidence (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source
      (RecursiveNamedExpressionCompilerCertificates.RuntimeExpressionsWith (some evidence) headers callerCompilation fuel source context solved reasonAt) faults
      (protectedEntry headers locations capturePrefix callerCompilation.administrativePrefix) := by
  exact expression_reflects_at_with_evidence true true functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles evidence valid callerUninitialized callerMissing size


end RuntimeEvidence

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

section Formation
variable {values : SourceCoreCompatibleValues.Context}
  {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
  {program : Program} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : Inventory indexed.ancestry values indexed.layouts.definitions program} {locations : Locations}
  {expressionSyntax : Header indexed.ancestry values indexed.layouts.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (profile : values.checked.catalog.callableContracts = true)


abbrev FormationExpressions (authenticated : Bool)
    (header : Header indexed.ancestry values indexed.layouts.definitions program)
    (context : SourceSemantics.Context) :=
  RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := header) (headers := headers)
    (context := context) (evidence := header.function.evidence) (registry := registry) (faults := faults)
    (fuel := header.readFuel) (solved := header.solved) (reasonAt := header.reasonAt) authenticated

abbrev FormationProfile (authenticated : Bool)
    (header : Header indexed.ancestry values indexed.layouts.definitions program) (administrative : Core.Context) :=
  MatchProfileWith (ambient := CallableIndexedAmbient.ambientDefinitions indexed) (fun context => CompatibleRuntimeContextValidity.Valid header.solved context header.function.evidence)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated header)
    diagnosticPolicy header (expressionSyntax header) administrative registry faults

variable (authenticated : Bool)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers)
  (alignments : ∀ header, header ∈ headers → RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header
    (CallableIndexedNamedGeneration.context indexed header.named) 0)
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (owners : (program.functions.map (fun definition => definition.body.owner)).Nodup)
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      (entry : BodyState (ambient := CallableIndexedAmbient.ambientDefinitions indexed) headers locations 0 (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header
        arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost) →
      RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry entry →
      FormationProfile (headers := headers) (registry := registry) (faults := faults) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) authenticated header
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))

include complete alignments extension owners uninitialized missing escaped profiles in
/-- The same strong induction closes formation inside every actual named callee.
Its static provider is restricted to independently aligned parameter states. -/
theorem preserves_at_formation (size : Nat) :
    ∀ header, header ∈ headers → BodyPreservesAtWith
      (headers := headers) (locations := locations) (capturePrefix := 0) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header faults
      (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry) size := by
  apply preserves_at_with_family (locations := locations) (capturePrefix := 0) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) true (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) extension (CallableIndexedLambdaValues.identity_faithful indexed)
    (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile) escaped
    (fun header => RecursiveNamedLambdaFormationEntries.protectedEntry
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header headers locations 0 1)
    (fun _ => RecursiveNamedLambdaFormationEntries.transport) (fun _ => RecursiveNamedLambdaFormationEntries.binds)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated)
    profiles _ size
  intro header member context valid budget child within bodies
  exact RecursiveNamedLambdaFormationTreeMeaning.preserves_at profile complete alignments (alignments header member) extension
    header.unique owners (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within bodies

include complete alignments extension uninitialized missing escaped profiles in
/-- Reflection consumes original strict body children and returns independent
source grades. No body preservation or source trace is an input. -/
theorem reflects_at_formation (size : Nat) :
    ∀ header, header ∈ headers → BodyReflectsAtWith
      (headers := headers) (locations := locations) (capturePrefix := 0) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry header faults
      (RecursiveNamedLambdaFormationEntries.BodyAligned (indexed := indexed) (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) registry) size := by
  apply reflects_at_with_family (locations := locations) (capturePrefix := 0) (expressionSyntax := expressionSyntax) (diagnosticPolicy := diagnosticPolicy) true (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile) extension (CallableIndexedLambdaValues.identity_faithful indexed)
    (CallableIndexedLambdaRuntimeValues.observations indexed program registry faults profile)
    (CallableIndexedLambdaRuntimeValues.runtime_views indexed program registry faults profile) escaped
    (fun header => RecursiveNamedLambdaFormationEntries.protectedEntry
      (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed header headers locations 0 1)
    (fun _ => RecursiveNamedLambdaFormationEntries.transport) (fun _ => RecursiveNamedLambdaFormationEntries.binds)
    (FormationExpressions (headers := headers) (registry := registry) (faults := faults) authenticated)
    profiles _ size
  intro header member context valid budget child within bodies
  exact RecursiveNamedLambdaFormationTreeMeaning.reflects_at profile complete alignments (alignments header member) extension
    (uninitialized header member) (missing header member) authenticated valid.ledger valid.runtime budget child within bodies

variable {caller : Header indexed.ancestry values indexed.layouts.definitions program}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {solved : List SolvedRequirement} {fuel : Nat} {reasonAt : ExpressionId → Word}
  (callerAligned : RecursiveNamedLambdaFormationEntries.FormationHeader
    (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller
    (CallableIndexedNamedGeneration.context indexed caller.named) 0)
  (valid : CompatibleRuntimeContextValidity.Valid solved context evidence)
  (callerUninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (callerMissing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))

include complete alignments extension owners uninitialized missing escaped profiles callerAligned valid callerUninitialized callerMissing in
/-- Whole expressions use the same closed named-callee induction. Formation
receipts stay in the fixed model through both arguments and full heaps. -/
theorem expression_preserves_at_formation (size : Nat) :
    RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := caller) (headers := headers)
        (context := context) (evidence := evidence) (registry := registry) (faults := faults)
        (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  exact RecursiveNamedLambdaFormationTreeMeaning.preserves_at profile complete alignments callerAligned extension
    caller.unique owners callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl _)
    (fun header member child _ => preserves_at_formation profile authenticated complete alignments extension owners
      uninitialized missing escaped profiles child header member)

include complete alignments extension uninitialized missing escaped profiles callerAligned valid callerUninitialized callerMissing in
/-- Original native completion returns source evaluation through that same
closed family; no source trace or body law is supplied. -/
theorem expression_reflects_at_formation (size : Nat) :
    RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry
        (CallableIndexedLambdaRuntimeValues.model indexed program registry faults profile))
      program context evidence caller.function.source
      (RecursiveNamedLambdaFormationTreeMeaning.Expressions (caller := caller) (headers := headers)
        (context := context) (evidence := evidence) (registry := registry) (faults := faults)
        (fuel := fuel) (solved := solved) (reasonAt := reasonAt) authenticated) faults
      (RecursiveNamedLambdaFormationEntries.protectedEntry
        (ambient := CallableIndexedAmbient.ambientDefinitions indexed) indexed caller headers locations 0 1) := by
  exact RecursiveNamedLambdaFormationTreeMeaning.reflects_at profile complete alignments callerAligned extension
    callerUninitialized callerMissing authenticated valid.ledger valid.runtime size size (Nat.le_refl _)
    (fun header member child _ => reflects_at_formation profile authenticated complete alignments extension
      uninitialized missing escaped profiles child header member)

end Formation

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogMutualMeaning
