import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedTail
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedProjectedCommit
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTypedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPlaceAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStagedProjectedAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead

/-! Projected assignment heads run the ordered staged key row and the RHS at
their actual reached callers. A successful write keeps the saved target path,
the latest root and all compiler temporary slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentHeads
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CoreProof ReadOnly
open SourceCoreCompatibleDataPlaces GenericExpressionMeaning
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CellAwareInvocationExpressionBounds
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}

section Rhs
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {before targetHeap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate} {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
  {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
  (resolution : CompatibleCellPlaceResolution.Execution compiled.compatible.checked registry functions (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) prepared
    (CompatibleRenamedPlace.renamedCodes codes ξ) sourceTypes place leaf target actual store mapping world before targetHeap)

structure RhsResult (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap) (value : Value)
    (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop where
  trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap id outcome after
  evaluated : Evaluates
    (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values)
      (.inRight .unit resolution.snapshot) actual)
    resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore
  represented : RecursiveStageMeaning.ResultRepresentsFor (payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld node.type lowered.type faults outcome value
  heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore
  maps : LocationMap.Extends resolution.mapping finalMap
  worlds : WorldExtends resolution.world finalWorld
  frame : AdministrativePreserved resolution.mapping resolution.store finalMap finalStore
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) resolution.mapping resolution.world targetHeap resolution.store finalMap finalWorld after finalStore
  sourcePost : ∀ right, outcome = .value right →
    Dynamic.ValueHasType context after right node.type ∧ Dynamic.HeapWellTyped context after

theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active resolution.mapping resolution.world targetHeap resolution.store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical resolution.mapping resolution.world targetHeap resolution.store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment targetHeap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      RhsResult (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (.cons (.inRight resolution.snapshotRelated.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
          (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))) initial admitted authority physical owner ownerFrame trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      resolution.mapping resolution.world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) resolution.mapping resolution.world targetHeap resolution.store)
    (locals : Dynamic.EnvironmentAgrees targetHeap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active resolution.mapping resolution.world targetHeap resolution.store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical resolution.mapping resolution.world targetHeap resolution.store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (ownerFrame : owner.key.frameLocation = physical.location)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType resolution.target (DataPatternValues.packValues resolution.values) (.inRight .unit resolution.snapshot) actual)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RhsResult (environment := environment) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        resolution sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, DataPatternValues.packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (.cons (.inRight resolution.snapshotRelated.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
          (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))) initial admitted authority physical owner ownerFrame
      (by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
        DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld,
    ⟨trace, evaluated.sound, represented, finalHeaps, maps, worlds, frame, metadata, effect, by
      intro right same
      cases same
      exact ⟨post.at_value.1, post.at_value.2.heap⟩⟩, reached, related⟩
end Rhs

theorem tree_typed {source : TypedSource} {context : SourceSemantics.Context}
    {certificate : Certificate} {scope : Scope} {ids : List ExpressionId} {types original : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes)
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids original) :
    ExpressionsHaveTypes source context ids types := by
  have members : ∀ id, id ∈ ids → ∀ node, source.lookupExpression? id = some node → ExpressionHasType source context id node.type :=
    fun _ member _ found => CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique typed member found
  clear typed
  induction tree with
  | nil => exact .nil _
  | single found _ => exact .cons (members _ (by simp) _ found) (.nil _)
  | cons found _ _ ih =>
      exact .cons (members _ (by simp) _ found) (ih (fun id member => members id (List.mem_cons_of_mem _ member)))

inductive ResultAt (size : Nat)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | keyFault {keySize : Nat} {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target)
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | getterFault {keySize : Nat} {sources : List Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) after)
      (failed : Staging.Recursive.ProjectedTarget.GetterFault environment before after assignment.target sources reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | rhsFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | writeFault {keySize sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap}
      {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) after)
      {reason : Dynamic.SemanticFault}
      (failed : Staging.Recursive.ProjectedTarget.WriteFault operator target right after reason)
      (same : value = .inLeft output (.word token)) (matched : faults (.semantic reason) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {keySize sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      {sources : List Dynamic.Value} {targetHeap : Dynamic.Heap}
      (keys : Staging.Recursive.Size.Expressions program stages keySize invocation context environment before
        (Staging.Recursive.ProjectedTarget.keys assignment.target.projections) (.values sources) targetHeap)
      (snapshot : Staging.Recursive.ProjectedTarget.Snapshot environment before targetHeap assignment.target sources target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated after)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after written)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext compiled.indexed.layouts.definitions)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (related : callerProtocol.Relates initial reached) (admitted : Admission bridge context reached)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (shift 7 next) value finalStore) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationProjectedAssignmentHeads
