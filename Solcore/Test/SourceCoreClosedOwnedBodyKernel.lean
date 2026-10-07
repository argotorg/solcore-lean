import Solcore.Test.SourceCoreClosedOwnedLexicalBody
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMarkedAllocation
import Solcore.SourceSemantics.CoreLowering.CallableRuntimeBodyMutualMeaning

/-! A real lexical static receipt embeds into the general body Tree and its
CatalogSites. Empty expression certificates close the actual body kernel and
family without an assumed expression or body meaning. -/
set_option autoImplicit false
namespace Tests.SourceCoreClosedOwnedBodyKernel
open Solcore Core Frontend SourceInference
open SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState
open ProtectedStateTransition
open Tests.SourceCoreClosedOwnedLexicalBody (noExpressions noExpressionSyntax reached_pool_observations)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}

private def ownedProducer {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment}
    (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions) :
    MarkedAllocation.Producer (protocol headers keys) compiled.indexed.layouts
      compiled.indexed.ancestry.layout.frame model := by
  subst definitions
  exact CallableIndexedOwnedMarkedAllocation.producer headers keys model

private theorem acquire {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (sameDefinitions : compiled.indexed.layouts.definitions = definitions)
    (location : Location) (native : NativeFrame)
    (seed : CallableIndexedOwnedAllocationProducer.StableOwner keys location native) :
    OrdinaryAllocation.ReadyAt (ownedProducer (headers := headers) (keys := keys) model sameDefinitions).toOrdinary location native := by
  subst definitions
  exact CallableIndexedOwnedAllocationProducer.readyAt_of_stableOwner model seed

private theorem no_expression_preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {faults : FunctionCalls.FaultRep} (size : Nat) :
    ProtectedStateTransition.PreservesAt (protocol headers keys) model program context evidence source
      (noExpressions context) faults size := by
  intro scope id lowered impossible
  cases impossible

private theorem no_expression_reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {faults : FunctionCalls.FaultRep} (size : Nat) :
    ProtectedStateTransition.ReflectsAt (protocol headers keys) model program context evidence source
      (noExpressions context) faults size := by
  intro scope id lowered impossible
  cases impossible

section Body
open RecursiveNamedCallBounds (BodyTrace)
variable {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {globals : Nat} {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {function : Dynamic.Closure}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (functionTypes : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)
  (registered : compiled.indexed.ancestry.layout.frame.Registered ambient.definitions)
  {solved : List SolvedRequirement}
  (valid : CompatibleRuntimeContextValidity.Valid solved context function.evidence)
  (unitResult : function.resultType = .unit)
  (admission : GenericLexicalStatements.Syntax function.source noExpressionSyntax context true function.body function.resultType)
  {flow code : Expr} {fellThrough escaped : Word}
  (tree : GenericLexicalStatements.Tree compiled.indexed.layouts owner active compiled.indexed.ancestry.layout.frame
    globals onError values function.source noExpressions context scope true function.body function.resultType .unit flow)
  (emitted : code = CompatibleStatements.finish .unit flow fellThrough escaped)
  (unique : NodeOccurrencesUnique function.source) (escapedFault : faults .controlEscapedFunction escaped)

private def kernel : CallableRuntimeBodyKernel.BodyFor compiled.indexed.layouts owner active
    compiled.indexed.ancestry.layout.frame globals onError values function noExpressionSyntax noExpressions
    (fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence)
    .reachable ambient administrative context scope .unit code fellThrough escaped registry faults where
  flow := flow
  tree := GenericImperativeMatch.Tree.body admission tree
  sites := .body (syntaxTree := admission) (body := tree)
  initialValid := valid
  projection := by rw [unitResult]; rfl
  unique := unique
  emitted := emitted

include definitions registered extension faithful observations valid unitResult admission tree emitted unique escapedFault in
/-- Source body execution closes through the real lexical Tree and native
finish. Every state callback is derived here from static receipts. -/
theorem closed_kernel_preserves (size : Nat)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {outcome : Dynamic.ExpressionOutcome}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (trace : BodyTrace program size function context environment before outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType .unit faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    CallableRuntimeBodyKernel.Stateful.BodyFor.preserves_sized
      (body := kernel valid unitResult admission tree emitted unique)
      (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
      (program := program) (faithful := faithful) (observations := observations) (escapedFault := escapedFault)
      (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
      (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (acquire := acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (stateTransport := administrativeTransport headers keys) (stateBindings := CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      size size (Nat.le_refl _) (fun _ _ child _ => no_expression_preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
      environments heaps locals agrees typed reference read unmapped initial seed trace
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩

include definitions registered extension faithful observations functionTypes valid unitResult admission tree emitted unique escapedFault in
/-- Reflection consumes the original native completion and constructs an
independent Source body grade, preserving its actual reached pool. -/
theorem closed_kernel_reflects (budget size : Nat) (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    {contextLocation : Location} {native : NativeFrame} {ghost : GhostFrame} {metadata : Option MetadataState}
    (initial : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
    (selected : Fin keys.length) (physicalOwner : keys[selected.val].frameLocation = contextLocation)
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef compiled.indexed.ancestry.layout.frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      BodyTrace program sourceSize function context environment before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        finalMap finalWorld function.resultType .unit faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      TypedMixedNamedBody.ReachedExit values.checked ambient.definitions finalMap finalWorld administrative program function
        context scope environment before after outcome ∧
      ∃ final : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates initial final ∧
        (∀ row, RecordPrefix (records initial row) (records final row)) ∧
        (∀ row record, record ∈ records final row → CallableIndexedSnapshots.Holds
          compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame finalMap finalStore record) ∧
        Transition (protocol headers keys) initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have seed : CallableIndexedOwnedAllocationProducer.StableOwner keys contextLocation native :=
    ⟨selected, ghost, metadata, physicalOwner, stable⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical, post⟩ :=
    CallableRuntimeBodyKernel.Stateful.BodyFor.reflects_sized
      (body := kernel valid unitResult admission tree emitted unique)
      (functions := functions) (definitions := definitions) (registered := registered) (extension := extension)
      (program := program) (faithful := faithful) (observations := observations) (functionTypes := functionTypes) (escapedFault := escapedFault)
      (extend := fun valid extended => valid.extend extended) (runtimeOf := fun valid => valid)
      (protocol := protocol headers keys) (conditionGate := CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (producer := ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (acquire := acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
      (stateTransport := administrativeTransport headers keys) (stateBindings := CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
      budget size within (fun _ _ child _ => no_expression_reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
      environments heaps locals agrees typed reference read unmapped initial seed evaluated
  obtain ⟨final, related⟩ := post
  obtain ⟨prefixes, snapshots, _oldMembers⟩ := reached_pool_observations related
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, preservation, heapMetadata, lexical,
    final, related, prefixes, snapshots, ⟨final, related⟩⟩
private def origin : CallableRuntimeBodyOrigins.StaticOrigin values ambient registry faults where
  layouts := compiled.indexed.layouts
  owner := owner
  active := active
  frameLayout := compiled.indexed.ancestry.layout.frame
  globals := globals
  onError := onError
  function := function
  expressionSyntax := noExpressionSyntax
  certificates := noExpressions
  validity := fun context => CompatibleRuntimeContextValidity.Valid solved context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := context
  scope := scope
  output := .unit
  code := code
  fellThrough := fellThrough
  escaped := escaped
  solved := solved
  body := kernel valid unitResult admission tree emitted unique
  definitions := definitions
  registered := registered
  escapedFault := escapedFault
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

include definitions registered extension faithful observations valid unitResult admission tree emitted unique escapedFault in
/-- A nonempty actual origin family closes with the static empty expression
certificate. No smaller callee or body semantic law is supplied. -/
theorem closed_family_preserves (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.preserves_at
    (fun (_ : Unit) => origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault)
    functions extension program faithful observations (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ _ _ _ child _ _ => no_expression_preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    size ()

include definitions registered extension faithful observations functionTypes valid unitResult admission tree emitted unique escapedFault in
/-- Actual native family reflection closes separately and returns an
independent source grade from the original measured completion. -/
theorem closed_family_reflects (size : Nat) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) functions program
      (origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault) size := by
  exact CallableRuntimeBodyMutualMeaning.Stateful.reflects_at
    (fun (_ : Unit) => origin (registry := registry) (administrative := administrative) definitions registered valid unitResult admission tree emitted unique escapedFault)
    functions extension program faithful observations functionTypes (protocol headers keys)
    (fun _ => CallableIndexedOwnedAllocationProducer.StableOwner keys)
    (fun _ => ownedProducer (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (fun _ => acquire (CompatibleAmbientHeap.payloadModel values.checked registry functions) definitions)
    (administrativeTransport headers keys) (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys)
    (fun _ _ _ _ child _ _ => no_expression_reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions) child)
    size ()

end Body

end Tests.SourceCoreClosedOwnedBodyKernel
