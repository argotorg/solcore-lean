import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceReflection

/-!
# Compatible profile: typed places

Keys, resolution, faults and reflection of typed places.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
/-! The saved snapshot, packed keys and captured root reference are the actual
three RHS slots. Their typing is derived from resolution receipts and the
canonical lexical environment, rather than supplied as a child execution.
The result and latest-root relations are shared with unrestricted RHS meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhs

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Every hidden slot uses the post-getter world. Existing administrative
captures are transported by the exact world extension from resolution. -/
theorem snapshot_runtimeTyped {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {scope : Scope}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      initialMap initialWorld administrativeContext scope environment coreEnvironment) :
    RuntimeEnvironmentHasTypes resolution.world
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      (OptionalCell.cellType prepared.route.leafType :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
  .cons (.inRight resolution.snapshotRelated.runtime_hasType)
    (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
      (.cons (.cellRef resolution.reference.typed)
        (environments.extend resolution.maps resolution.worlds).runtime_hasTypes))

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem preserves
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  have actualTyped := snapshot_runtimeTyped resolution environments
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) actualTyped trace
  refine ⟨value, store, mapping, world, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 lowered.expression) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  have actualTyped := snapshot_runtimeTyped resolution environments
  obtain ⟨outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) actualTyped
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, mapping, world, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceRhs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceFailures
/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
universal expression IH; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceFailures
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before place.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves_fault children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees layout [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) environments.runtime_hasTypes) trace
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  apply execute_key_failure prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var coreLookup)
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- This composition consumes a semantic resolution result, produced by
CompatibleTypedPlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
theorem rhs {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {administrativeContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨value, store, mapping, world, result⟩ :=
    CompatibleTypedPlaceRhs.preserves resolution meaning generated found environments locals (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var index) (SourceCoreCalls.packArguments codes)
      lowered.expression next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceFailures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetKeys
/-! Typed child meanings for the actual CompatiblePlaceTargetKeys phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTargetKeys

/-- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place codes sourceTypes location resolved coreEnvironment before after store mapping world index) := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) environments.runtime_hasTypes) trace
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    related, keyHeaps, maps, worlds, frame, metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetKeys
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetFaults
/-! Target-resolution faults before the RHS. The actual key runs are derived
from the universal expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetFaults
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext : Core.Context}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

/-- Independent structural failure determines the actual whole emitted
assignment's failure before its RHS, modifier, setter or continuation starts. -/
theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨keys⟩ := CompatibleTypedPlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup initialRead trace
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists : ∃ optional rootValue,
      RootRead compilation.checked registry functions keys.keyMap keys.keyWorld prepared after keys.keyStore location keys.target
        currentCell optional sourceRoot rootValue := by
    cases initialValue with
    | initialized =>
      obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keys.heaps keys.reference currentRead
      exact ⟨_, value, root⟩
    | emptyMapping key value =>
      obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keys.heaps keys.reference currentRead
        (layout.virtual key value cellType.symm) registryExtension
      exact ⟨_, native, root⟩
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have arguments := layout.views.arguments keys.shaped keys.related (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keys.related.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keys.related)
      (.cons (.cellRef keys.reference.typed) ((environments.extend keys.maps keys.worlds).runtime_hasTypes))
  obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
    evaluation_frame (mapping := keys.keyMap) keys.heaps.runtime_hasTypes typedEnvironment layout.getterTyped evaluated appended
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata⟩
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

/-- Actual describe supplies `ordinary`. It is a static route fact, not a
claim that native type equality recovers the source declaration. -/
theorem uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨keys⟩ := CompatibleTypedPlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup initialRead trace
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference currentRead
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata⟩
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceTargetFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceResolution
/-! Typed child meanings for the actual CompatiblePlaceResolution phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceResolution

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

/-- Successful source resolution constructs the actual key and getter runs.
The universal child theorem covers every intermediate key heap and hidden
reference slot. Independent writable-local typing and environment agreement
recover the exact raw root declaration type. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution compilation.checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro _ _ found; exact found
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      TypedDataPlaceKeyOrder.preserves children meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
        (.cons (.cellRef reference.typed) environments.runtime_hasTypes) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := keyMap) keyHeaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := evaluated
              keysRelated := keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceStructuralFault
/-! Structural missing-default failure after the RHS. The source specification
traverses the latest root before applying the modifier. For authenticated equal
or scalar numeric operands, the generated earlier modifier is total; therefore
the same structural fault wins and neither source nor native final write runs.
Exact raw key guards come from the source fault, not native projection equality.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceStructuralFault
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

/-- All key/RHS native evaluations come from their universal IH. The fault
receipt retains the raw mapping header and ordered selection where traversal
stopped; no decoder or source evaluator supplies the semantic result. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve evaluate sourceRead rootType initialValue fault
  obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
    environments heaps locals slot rootTyped resolve
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    CompatibleTypedPlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep := resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
      CompatiblePlaceModifier.initialized_outcome observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          ((environments.extend (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)).runtime_hasTypes)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, _, _⟩ :=
      CompatiblePlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata⟩
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ resolution.snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceStructuralFault
end

section
/-! A compound operation that panics after the RHS. The latest root is
traversed, so the native setter runs; the modifier's check then fails with the
panic's reason before the write, and the source writes nothing either. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlacePanic
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_read {projections : List Dynamic.EvaluatedProjection} {selected : Option Dynamic.Value}
    (read : Dynamic.ProjectionsRead none projections selected) : projections = [] := by
  cases read
  rfl

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell}
    {initial currentSelected : Option Dynamic.Value} {code : UInt8}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (pathRead : Dynamic.ProjectionsRead initial sourceTarget.projections currentSelected)
    (panics : Dynamic.AssignmentOperandsPanic operator sourceTarget.selected right code)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word (SourceCorePanics.reason code))) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
    environments heaps locals slot rootTyped resolve
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
    CompatibleTypedPlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep := resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, modifiedEvaluated, outcome⟩ :=
      CompatiblePlaceModifier.initialized_outcome observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    rw [resolution.selectedEq] at panics
    -- The panic fixes a panicking modifier, a zero divisor and its code.
    obtain ⟨operation, selected, zero, sameCode⟩ : ∃ operation,
        binaryOperator (prepared.route.leafType = .integer) operator = some ⟨operation, true⟩ ∧
          rightValue = .word Word.zero ∧ code = SourceCorePanics.divisionByZero := by
      rcases outcome with ⟨applied, _⟩ | ⟨operation, selected, zero, other⟩
      · exact (CompatiblePlaceModifier.panic_excludes_applies panics applied).elim
      · exact ⟨operation, selected, zero, CompatiblePlaceModifier.panic_functional panics other⟩
    subst zero sameCode
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_read pathRead)).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨_, changed⟩ := DataPlaceUpdateTotality.read_update pathRead replacement
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) (.word Word.zero) replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          ((environments.extend (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)).runtime_hasTypes)))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨_, helperStore, futureWorld, setterEvaluated, helperHeaps, extension, frame⟩ :=
      CompatiblePlaceWriteback.setter_preserves root rhsResult.heaps currentArguments replacementRep changed layout.nonempty
        faithful observations keyLength typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
    refine ⟨helperStore, rhsMap, futureWorld, ?_, helperHeaps, resolution.maps.trans rhsResult.maps,
      (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
      resolution.metadata.trans rhsResult.metadata⟩
    refine .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ resolution.snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_success _ setterEvaluated ?_)))))
    rw [selected]
    exact SourceCoreDataPlaces.guard_panic

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlacePanic
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
/-! Every independently specified assignment fault in the nonempty equal or
numeric profile is preserved. Unbound/dangling roots contradict actual lexical
and heap agreement. Invalid operands contradict the represented snapshot and
RHS values; neither exclusion is inferred from native type equality alone. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, sourceCell, sourceLookup, sourceRead, _, _⟩ := locals.lookup staticLookup
  cases trace with
  | target fault =>
    cases fault with
    | unbound missing => exact (missing.excludes_lookup sourceLookup).elim
    | dangling lookup missing =>
      have same := lookup.functional sourceLookup
      cases same
      exact (missing.excludes_read sourceRead).elim
    | projectionExpression lookup read fault =>
      obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceFailures.keys layout.children meaning environments heaps locals slot lookup read fault
          operator rhs lowered.expression next outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
    | danglingAfterProjections lookup read evaluated missing =>
      obtain ⟨keys⟩ := CompatibleTypedPlaceTargetKeys.preserves layout.children meaning environments heaps locals slot rootTyped lookup read evaluated
      exact (missing.excludes_read keys.read).elim
    | projectionRead lookup initialRead evaluate currentRead initialValue fault =>
      obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceTargetFaults.projection layout meaning environments heaps locals slot rootTyped lookup initialRead evaluate currentRead
          registryExtension faithful observations initialValue fault operator rhs lowered.expression next outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩
    | uninitialized lookup initialRead evaluate currentRead empty notMapping projected =>
      obtain ⟨finalStore, finalMap, finalWorld, _, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
        CompatibleTypedPlaceTargetFaults.uninitialized layout meaning environments heaps locals slot rootTyped lookup initialRead evaluate currentRead
          ordinary empty notMapping projected operator rhs lowered.expression next outputType invalid
      exact ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, evaluated, invalidTokens _, finalHeaps, maps, worlds, frame, metadata⟩
  | rhs resolve fault =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleTypedPlaceFailures.rhs resolution meaning rhsGenerated found rhsCoreType environments locals resolve coreLookup fault
        operator next outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩
  | operands resolve evaluate _ _ _ _ invalidOperands =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatibleTypedPlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf _ rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
      have valid := CompatiblePlaceModifier.initialized_valid observations operatorProfile rhsResult.saved_snapshot rightRep
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
  | panic resolve evaluate currentRead _ initialValue pathRead panics =>
    obtain ⟨finalStore, finalMap, finalWorld, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleTypedPlacePanic.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals slot rootTyped resolve evaluate currentRead initialValue pathRead panics
        next outputType invalid
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, FunctionCalls.FaultTokens.panic _, finalHeaps, maps, worlds, frame, metadata⟩
  | structuralUpdate resolve evaluate currentRead sameType initialValue fault =>
    obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩ :=
      CompatibleTypedPlaceStructuralFault.preserves layout registryExtension meaning faithful observations rhsGenerated found rhsView rhsCoreType
        operatorProfile environments heaps locals slot rootTyped resolve evaluate currentRead sameType initialValue fault next outputType invalid
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingTokens receipt, finalHeaps, maps, worlds, frame, metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeyReflection
/-! Typed child meanings for the actual CompatiblePlaceKeyReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeyReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection

/-- Completed emitted code supplies the key runs to the universal reflection
IH. No source projection trace or child runtime execution is an input. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid) result finalStore) :
    Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) keyValue keyStore) =>
    TypedDataPlaceKeyOrder.reflects children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) environments.runtime_hasTypes)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var selected)
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | @values sources values related =>
        cases sourceTrace with
        | @values _ resolved _ shaped sourceTrace =>
          obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional staticLookupRuntime
          subst staticLocation
          have cellEq := initialRead.functional staticRead
          subst staticCell
          obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
          exact .keys lookup sourceTrace
            ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
              type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, selected, shaped,
              keysEvaluated, related, finalHeaps, maps, worlds, frame, metadata⟩ tail

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeyReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlacePrefixReflection
/-! Typed child meanings for the actual CompatiblePlacePrefixReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlacePrefixReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlacePrefixReflection

/-- The diagnostic premises are static interpretations of emitted tokens.
They do not supply any source or native execution. All target source traces
are reconstructed from a completed emitted assignment and universal child IH. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := CompatibleTypedPlaceKeyReflection.reflects layout.children meaning environments heaps locals slot rootTyped lookup initialRead completed
  cases keyPhase with
  | fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata
  | @keys sourceLocation resolved after keyLookup sourceTrace keys continuation =>
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have arguments := layout.views.arguments keys.shaped keys.related (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keys.related)
        (.cons (.cellRef keys.reference.typed) ((environments.extend keys.maps keys.worlds).runtime_hasTypes))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatiblePlaceGetterReflection.reflects currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keys.related.length.2)
        keys.heaps keys.reference keys.read typedEnvironment layout.getterTyped (.var rfl) (.var rfl) evaluated
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | missing initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.projectionRead lookup initialRead sourceTrace keys.read initial fault) rfl
              (missingTokens receipt) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.uninitialized lookup initialRead sourceTrace keys.read empty notMapping nonempty) rfl
              (invalidTokens _) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | @read sourceRoot selected snapshot initial read represented =>
        exact .resolved (.intro lookup initialRead sourceTrace keys.read initial read)
          { target := keys.target
            sources := keys.sources
            values := keys.values
            selected := selected
            snapshot := snapshot
            keyStore := keys.keyStore
            store := _
            mapping := keys.keyMap
            world := futureWorld
            selectedEq := rfl
            currentCell := keys.cell
            currentRead := keys.read
            currentType := keys.type
            reference := keys.reference.extend (.refl _) extension
            shaped := keys.shaped
            keysEvaluated := keys.evaluated
            snapshotEvaluated := getterEvaluated
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata } remaining

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlacePrefixReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentSuccess
/-! Typed successful assignment prefixes expose their seven real temporary
values. Getter/setter typing and represented payloads type those slots in the
post-write world; no arbitrary slot list is assumed to be safe for captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentSuccess
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: prepared.route.leafType ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/-- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
          (slots ++ coreEnvironment) finalStore (shift 7 next) := by
  cases trace with
  | @intro _ _ _ _ _ _ targetHeap rhsHeap _ _ sourceTarget _ right _ resolve evaluate written =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleTypedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty layout.getterTyped meaning faithful observations
      environments heaps locals slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatibleTypedPlaceRhs.preserves resolution meaning rhsGenerated found environments locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCoreType] using rightRep)
      have snapshotRep := rhsResult.saved_snapshot
      have keyRep := resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
      have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
      have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
      obtain ⟨latest⟩ := rhsResult.latest
      cases written with
      | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
        have cellEq := sourceRead.functional latest.read
        have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
        obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
        rw [resolution.selectedEq] at applies
        obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
          CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
        have passes := CompatiblePlaceModifier.passes_of_applies observations operatorProfile rightRep applies
          (prepared.route.leafType = .integer)
        have present : ∃ sourceRoot, initial = some sourceRoot := by
          cases initial with
          | some value => exact ⟨value, rfl⟩
          | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
        obtain ⟨sourceRoot, rfl⟩ := present
        have rootExists : ∃ optional rootValue,
            RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
              cell optional sourceRoot rootValue := by
          cases initialValue with
          | initialized =>
            obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
            exact ⟨_, value, root⟩
          | emptyMapping key value =>
            obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
              (layout.virtual key value cellType.symm) registryExtension
            exact ⟨_, native, root⟩
        obtain ⟨optional, rootValue, root⟩ := rootExists
        have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
        have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
            (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
            (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
              OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
            ambient.definitions :=
          .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
            (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
              ((environments.extend (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)).runtime_hasTypes)))))
        have currentPath : PreparedPath compilation.checked source site cell.type place.projections
            0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
        have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
            currentPath sourceTarget.projections := by simpa only [cellType] using arguments
        obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
          helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
          CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
            faithful observations keyLength typedEnvironment layout.setterTyped (.var rfl) (.var rfl) (.var rfl)
        refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
          by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
          (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
          (resolution.metadata.trans rhsResult.metadata).trans metadata,
          [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
            packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_⟩
        · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
        · intro next outputType
          exact (ContinuationAgreement.letE (.var coreLookup)).trans
            ((ContinuationAgreement.bind resolution.keysEvaluated).trans
              ((ContinuationAgreement.bind resolution.snapshotEvaluated).trans
                ((ContinuationAgreement.bind rhsResult.evaluated).trans
                  ((ContinuationAgreement.bind modifiedEvaluated).trans
                    ((ContinuationAgreement.bind setterEvaluated).trans
                      ((DataPlaceGuard.agreement passes).trans
                        (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten))))))))

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentReflection
/-! Completed emitted assignment reconstructs independent target/RHS/write
traces using typed children. On success the reconstructed finite prefix also
certifies the actual seven continuation slots, before any next statement runs.
The profile retains a static nonempty path layout, raw key views, diagnostics,
and equal/Word/Integer operator admission. Bare-root writes are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhsReflection

/-- Source and Core RHS types are connected by the retained raw runtime view,
not by inverting the many-to-one native type projection. -/
private theorem rhs_reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : CompatiblePlacePrefixReflection.Result checked registry functions program context evidence source faults prepared codes sourceTypes
      place leaf environment coreEnvironment before store mapping world lowered.expression next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked registry functions program context evidence source faults prepared codes sourceTypes place leaf environment
      coreEnvironment before store mapping world id node lowered next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatibleTypedPlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
      cases represented : rhsResult.represented with
      | fault tokenRep =>
        cases rhsResult.trace with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsResult.heaps
                (resolution.maps.trans rhsResult.maps) (resolution.worlds.trans rhsResult.worlds)
                (resolution.frame.trans rhsResult.frame) (resolution.metadata.trans rhsResult.metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, rhsResult⟩ :=
        CompatibleTypedPlaceRhs.reflects resolution meaning generated found environments locals rhsEvaluated
      cases represented : rhsResult.represented with
      | value payload =>
        exact .ready sourceTrace resolution
          { right := _
            value := _
            heap := rhsHeap
            store := _
            mapping := rhsMap
            world := rhsWorld
            meaning := rhsResult
            related := .compatible rhsView (by simpa only [payloadModel, coreType] using payload) } remaining

theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (preservation : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result finalStore) :
    (∃ reason token after finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      result = .inLeft outputType (.word token) ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after) ∨
    (∃ updated after written finalMap finalWorld slots,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after written ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap written ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧
      RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
        (CompatibleTypedPlaceAssignmentSuccess.writtenContext prepared (SourceCoreCalls.packArguments codes).type
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions ∧
      Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) := by
  have resolution := CompatibleTypedPlacePrefixReflection.reflects layout ordinary registryExtension meaning functionTypes faithful observations
    missingTokens invalidTokens environments heaps locals slot rootTyped completed
  have rhsResult := rhs_reflects meaning rhsGenerated found rhsView rhsCoreType environments locals resolution
  have observed : CompatiblePlaceTailReflection.Result compilation.checked registry functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
    cases rhsResult with
    | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
      exact .fault sourceFault resultEq tokenRep heaps maps worlds frame metadata
    | ready sourceTrace resolution right continuation =>
      exact CompatiblePlaceTailReflection.reflects_ready layout ordinary registryExtension functionTypes faithful observations missingTokens
        operatorProfile environments sourceTrace resolution right continuation
  cases observed with
  | fault trace resultEq matched finalHeaps maps worlds frame metadata =>
    exact .inl ⟨_, _, _, _, _, trace, resultEq, matched, finalHeaps, maps, worlds, frame, metadata⟩
  | committed trace _ _ _ _ _ _ _ =>
    obtain ⟨nativeRoot, written, finalMap, finalWorld, rootRep, finalHeaps, maps, worlds, frame, metadata,
      slots, length, typed, agreement⟩ :=
      CompatibleTypedPlaceAssignmentSuccess.preserves_prefix layout registryExtension preservation faithful observations
        rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals slot rootTyped trace invalid
    exact .inr ⟨_, _, written, finalMap, finalWorld, slots, trace, finalHeaps, maps, worlds, frame, metadata,
      length, typed, (agreement next outputType).unwrap completed⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceAssignmentReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
/-! Typed key computations produce the existing authenticated path Arguments.
Raw source type views stay explicit and are never inferred from native equality.
The unrestricted key API remains unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatibleMixedRoute CompatibleHeap CompatiblePlaceKeys

/-- Universal expression preservation constructs the key executions and their
intervening live heaps. This theorem adds path Arguments to the shared result. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {resolved : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues values)) finalStore ∧
      Arguments checked registry functions finalMap finalWorld source site values path resolved ∧
      HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, values, finalStore, finalMap, finalWorld, shaped, ran, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves tree meaning environments heaps locals layout actualTyped trace
  exact ⟨values, finalStore, finalMap, finalWorld, ran,
    views.arguments shaped represented (fun _ _ found => by simpa only [Nat.zero_add] using found), finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed packed-key computation reconstructs either the ordered
source key trace and authenticated path arguments, or its exact source fault. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store after : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (completed : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value after) :
    ∃ sourceAfter finalMap finalWorld,
      ((∃ values resolved,
        Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved sourceAfter ∧
        Arguments checked registry functions finalMap finalWorld source site values path resolved ∧
        value = .inRight .word (DataPatternValues.packValues values)) ∨
       (∃ reason token,
        Dynamic.SourceProjectionsFault program context evidence source environment before projections reason sourceAfter ∧
        faults reason token ∧ value = .inLeft (SourceCoreCalls.packArguments codes).type (.word token))) ∧
      HeapRepresents checked registry functions finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  obtain ⟨outcome, sourceAfter, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.reflects tree meaning environments heaps locals layout actualTyped completed
  refine ⟨sourceAfter, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | values shaped sourceTrace => cases represented with
    | values related => exact .inl ⟨_, _, sourceTrace,
        views.arguments shaped related (fun _ _ found => by simpa only [Nat.zero_add] using found), rfl⟩
  | fault sourceTrace => cases represented with
    | fault token => exact .inr ⟨_, _, sourceTrace, token, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
end
