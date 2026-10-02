import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceAssignmentContracts
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.ProtectedExpressionMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback

/-! Protected child meaning runs under the actual snapshot, packed keys and
captured root reference. The post-getter entry is derived from its real frame,
world and heap metadata receipts, never from environment typing alone. Their typing is derived from resolution receipts and the
actual environment typing, rather than supplied as a child execution.
The result and latest-root relations are shared with unrestricted RHS meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open CompatibleRenamedPlace
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhs

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Every hidden slot uses the post-getter world. Existing administrative
captures are transported by the exact world extension from resolution. -/
theorem snapshot_runtimeTyped {actualContext : Core.Context}
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions) :
    RuntimeEnvironmentHasTypes resolution.world
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      (OptionalCell.cellType prepared.route.leafType :: (SourceCoreCalls.packArguments (renamedCodes codes ξ)).type ::
        OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions :=
  .cons (.inRight resolution.snapshotRelated.runtime_hasType)
    (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
      (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem preserves_at (size : Nat)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped (transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata) trace
  refine ⟨value, store, mapping, world, trace.sound, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem reflects_at (size : Nat)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {value : Value} {store : Store}
    (evaluated : CoreProof.EvaluationSize size
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ sourceSize outcome after mapping world,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment targetHeap id outcome after ∧
      Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨sourceSize, outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped
      (transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, mapping, world, trace, trace.sound, evaluated.sound, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩

theorem preserves
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact preserves_at resolution size transport (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size)
    generated found environments agrees actualTyped locals installed sized

theorem reflects
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, mapping, world, _, result⟩ :=
    reflects_at resolution size transport (RecursiveNamedBoundedContracts.reflects_at_of_unbounded meaning size)
      generated found environments agrees actualTyped locals installed sized
  exact ⟨outcome, after, mapping, world, result⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload SourceCoreCompatibleDataPlaces CompatiblePlaceRhs

/-- The RHS result's real post-prefix map/world/protection receipts transport
all installed observations. Its three hidden slots never alter canonical
source scope or native captured closure environments. -/
theorem retained {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {types : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {target : Dynamic.ResolvedPlace} {actual canonical : Environment} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes types place leaf target
      actual initialStore initialMap initialWorld before targetHeap)
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world)
    {scope : Scope} {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (installed : entry scope initialMap initialWorld before initialStore canonical) :
    entry scope mapping world after store canonical :=
  transport.extend (transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata)
    result.maps result.worlds result.frame result.metadata

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceWriteback
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces

/-- The already-closed setter reconstruction and mapped write supply their
actual effects. The protected entry survives those exact effects; neither a
child evaluation nor a body semantics premise is supplied for writeback. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {prepared : Prepared} {heap after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {optional rootValue : Value}
    {sourceRoot : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {replacementSource updated : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked registry functions mapping world leaf replacementSource replacement prepared.route.leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some sourceRoot) projections updated)
    (written : Dynamic.Heap.Writes heap location (some updated) after)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment canonical : Environment} {actualContext : Core.Context} {keyType : Ty}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment actualContext ambient.definitions)
    (setterTyped : HasType actualContext
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement)
    {scope : Scope} {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (installed : entry scope mapping world heap store canonical) :
    ∃ native helperStore finalStore futureWorld,
      ValueRep checked registry functions mapping futureWorld cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) helperStore ∧
      helperStore.read? target = some optional ∧
      helperStore.write? target (.inRight .unit native) = some finalStore ∧
      HeapRepresents checked registry functions mapping futureWorld after finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧ entry scope mapping futureWorld after finalStore canonical := by
  obtain ⟨native, helperStore, finalStore, futureWorld, related, evaluated, read, write, finalHeaps,
    worlds, frame, metadata⟩ := CompatiblePlaceWriteback.preserves root heaps arguments replacementRep changed written
      nonempty faithful observations keyLength environmentTyped setterTyped referenceSelected keysSelected replacementSelected
  exact ⟨native, helperStore, finalStore, futureWorld, related, evaluated, read, write, finalHeaps, worlds, frame,
    metadata, transport.extend installed (.refl _) worlds frame metadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceWriteback
