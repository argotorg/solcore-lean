import Solcore.SourceSemantics.CoreLowering.ProtectedCellStagedBareAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentStatementHead

/-! Actual bare assignment Heads use the same admitted staged RHS and preserve
its exact reached caller. Source assignment typing establishes admission after
the write; failures keep the precise staged tag and the RHS endpoint. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareAssignmentHeads
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

variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry} {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyIndex : ActualBodyInvocation.Index compiled bodyRelation}

section Rhs
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {actual : Environment}
  {heap : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat}
  {faults : RecursiveStageMeaning.FaultRep} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {canonical : Environment}
  {certificate : Certificate}
  (snapshot : CompatibleBareAssignment.Snapshot compiled.compatible.checked registry functions prepared place environment actual heap store mapping world (ξ index))

private theorem rhs_preserves_at (size : Nat)
    (meaning : PreservesAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world heap store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages size invocation context environment heap id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      ProtectedCellStagedBareAssignment.RhsResult (cells := (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))) (instances := (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) (compilation := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot size outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted authority physical owner sameLocation trace
  refine ⟨value, finalStore, finalMap, finalWorld,
    ⟨trace, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, ?_⟩, reached, related⟩
  · simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, DataPlaceExecution.snapshotEnvironment,
    DataPlaceExecution.keysEnvironment, DataPlaceExecution.referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated
  · intro right same
    cases same
    exact ⟨post.at_value.1, post.at_value.2.heap⟩

private theorem rhs_reflects_at (size : Nat)
    (meaning : ReflectsAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults size)
    (generated : certificate scope id lowered) (found : invocation.source.lookupExpression? id = some node)
    (sourceTyped : ExpressionHasType invocation.source context id node.type)
    (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world heap store)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world heap store environment)
    (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world heap store environment)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
    (sameLocation : owner.key.frameLocation = physical.location)
    {value : Value} {finalStore : Store}
    (evaluated : EvaluationSize size
      (DataPlaceExecution.snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
      store (shift 3 (lowered.expression.rename ξ)) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedCellStagedBareAssignment.RhsResult (cells := (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment))) (instances := (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) (compilation := (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)) (program := program) (context := context)
        (stages := stages) (invocation := invocation) (faults := faults) (id := id) (node := node) (lowered := lowered)
        snapshot sourceSize outcome after value finalStore finalMap finalWorld ∧
      ProtectedStateTransition.Transition callerProtocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      effect, reached, related, post⟩ :=
    meaning generated found sourceTyped environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees
        [snapshot.value, .unit, .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target])
      (snapshot.runtimeTyped actualTyped) initial admitted authority physical owner sameLocation
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

inductive ResultAt (size : Nat)
    (context : SourceSemantics.Context) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (faults : RecursiveStageMeaning.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {failure : Staging.Recursive.Failure} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
      (same : value = .inLeft output (.word token)) (matched : faults failure token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | operands {sourceSize : Nat} {target : Dynamic.ResolvedPlace}
      {right : Dynamic.Value} {after : Dynamic.Heap} {current : Dynamic.Cell}
      {initialValue selected : Option Dynamic.Value} {token : Word}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
      (currentRead : Dynamic.Heap.Reads after target.location current)
      (rootType : current.type = target.rootType)
      (initialized : Dynamic.RootInitialValue current initialValue)
      (path : Dynamic.ProjectionsRead initialValue target.projections selected)
      (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right)
      (same : value = .inLeft output (.word token))
      (matched : faults (.semantic (.invalidAssignmentOperands operator)) token)
      (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore)
      (reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (related : callerProtocol.Relates initial reached) (stable : StableRows (bridge.pool reached)) :
      ResultAt size context stages invocation faults scope writtenContext assignment operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {target : Dynamic.ResolvedPlace}
      {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
      (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
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

section Heads
variable {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : Certificate} {scope : Scope} {administrative : Core.Context}
  (extension : SourceCoreRawMetadata.Extends ((SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)).registry registry)
  {faults : RecursiveStageMeaning.FaultRep}
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
  (head : GenericAssignmentStatements.Head (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) invocation.source context certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
  (bare : assignment.target.projections = [])
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {actualContext : Core.Context} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (definitions := compiled.indexed.layouts.definitions) (storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) bodyIndex.owner bodyIndex.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled bodyIndex context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)
  (unique : NodeOccurrencesUnique invocation.source)
  (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)

include extension environments heaps locals agrees bare head admitted in
/-- The accepted writable root and actual represented heap determine the
pre-RHS snapshot; no Source assignment execution is assumed. -/
theorem target_snapshot :
    ∃ target, Staging.Recursive.BareTarget environment before assignment.target target := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    obtain ⟨snapshot, _ordinary⟩ := @CompatibleBareAssignment.snapshot_of_cell_heap
      registry prepared assignment.target environment actual before store mapping world index
      (.initial compiled.compatible.checked) (CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      functions context scope administrative canonical ξ layout extension environments _
      GeneralizedLocalDescriptorHeap.ordinary_cells heaps admitted.heap locals agrees slot writable
    exact ⟨snapshot.resolved, .intro empty snapshot.lookup snapshot.read snapshot.root⟩

include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem reflects_bounded (budget : Nat)
    (boundedReflection : ReflectsBelow (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults budget)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid)
    {next : Expr} {output : Ty} {value : Value} {finalStore : Store}
    {size : Nat} (completed : EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAt (attachment := attachment) (registry := registry) bridge functions size context stages invocation faults
      scope (head.writtenContext actualContext) assignment operator rhs environment canonical actual
      before store mapping world initial (next.rename ξ) output value finalStore := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, right, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    have result := ProtectedCellStagedBareAssignment.reflects_with_rhs callerProtocol transport budget initial layout empty extension
      (fun snapshot child smaller {_ _} evaluated => rhs_reflects_at bridge functions snapshot child (boundedReflection child smaller)
        right found sourceTyped environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated)
      rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
      environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees actualTyped slot writable invalidToken completed bounded
    cases result with
    | fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .fault snapshot trace same matched finalHeaps maps worlds preservation metadata effect reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata effect post =>
      obtain ⟨reached, related⟩ := post
      exact .operands snapshot trace currentRead rootType initialized path invalidOperands same matched finalHeaps maps worlds preservation metadata effect reached related
        (StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation)
    | success snapshot trace rightTyped middleTyped write finalHeaps maps worlds preservation metadata effect count typed strict remaining post =>
      obtain ⟨reached, related⟩ := post
      exact .success snapshot trace write finalHeaps maps worlds preservation metadata effect count
        (by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
          Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed)
        reached related ⟨CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
          locals snapshot middleTyped rightTyped write,
          StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows preservation⟩ strict remaining
include transport extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_value {sourceSize : Nat}
    (meaning : PreservesAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults sourceSize)
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value} {middle after : Dynamic.Heap}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
      middle target updated after) :
    ∃ finalStore finalMap finalWorld slots,
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) compiled.indexed.layouts.definitions ∧
      (∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Admission bridge context reached) ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (shift 7 (next.rename ξ)) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨finalStore, finalMap, finalWorld, slots, rightTyped, middleTyped, finalHeaps, maps, worlds, frame, metadata, effect, count, typed, post, agreement⟩ :=
      ProtectedCellStagedBareAssignment.preserves_value_with_rhs callerProtocol transport initial layout empty extension snapshot trace write
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees actualTyped slot writable invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, effect, count,
      by simpa [GenericAssignmentStatements.Head.writtenContext, CompatibleRenamedPlaceSuccess.writtenContext, CompatibleBareAssignment.writtenContext,
        Prepared.optionalLeaf, SourceCoreCalls.packArguments, layout.sameType] using typed,
      ⟨reached, related, CallableIndexedOwnedBareAssignmentAdmission.heap_after_assignment unique found assignmentTyped
        locals snapshot middleTyped rightTyped write,
        StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩,
      agreement⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_fault {sourceSize : Nat}
    (meaning : PreservesAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults sourceSize)
    {failure : Staging.Recursive.Failure} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.fault failure) after)
    (next : Expr) (output : Ty) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults failure token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect, post⟩ :=
      ProtectedCellStagedBareAssignment.preserves_fault_with_rhs callerProtocol initial layout extension
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees slot writable next output invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

include extension environments heaps locals agrees actualTyped initial admitted unique assignmentTyped bare authority physical owner sameLocation in
theorem preserves_operands {sourceSize : Nat}
    (meaning : PreservesAt (attachment := attachment) bridge context (payloadModel compiled.compatible.checked registry functions) bodyIndex stages invocation certificate faults sourceSize)
    {right : Dynamic.Value} {after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (snapshot : Staging.Recursive.BareTarget environment before assignment.target target)
    (invalidOperands : Dynamic.AssignmentOperandsInvalid operator target.selected right)
    (trace : Staging.Recursive.Size.Expression program stages sourceSize invocation context environment before rhs (.value right) after)
    (next : Expr) (output : Ty)
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw
      (fun reason token => faults (.semantic reason) token) operator head.invalid) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧ faults (.semantic (.invalidAssignmentOperands operator)) token ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel (payloadModel compiled.compatible.checked registry functions) (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ StableRows (bridge.pool reached) := by
  rcases head with ⟨prepared, index, codes, leaf, lowered, node, invalid, shape, slot, writable, found, generated, rightView, rightType, profile⟩
  cases shape with
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))
  | bare empty layout =>
    have sourceTyped := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique found assignmentTyped
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect, post⟩ :=
      ProtectedCellStagedBareAssignment.preserves_operands_with_rhs callerProtocol initial layout empty extension snapshot invalidOperands
        (fun snapshot => rhs_preserves_at bridge functions snapshot sourceSize meaning generated found sourceTyped
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation trace)
        rightView rightType (CallableIndexedOwnedBareAssignmentAdmission.source_profile unique found assignmentTyped rightView)
        environments (GeneralizedLocalDescriptorHeap.ordinary_cells) admitted.heap heaps locals agrees slot writable next output invalid invalidToken
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, effect,
      reached, related, StableRows.after_administrative (bridge.pool initial) (bridge.pool reached) admitted.rows frame⟩

end Heads
end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationBareAssignmentHeads
