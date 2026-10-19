import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderPost
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileReady
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderControl

/-! Existing reachable diagnostic trees retain their original header prefix
contract. Their constructors cover allocations, expression discards, value
assignments and bare unary updates; no additional global model law is required. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalControl (allocate_absent allocate_initialized sequence_rename valid_extend)
open CallableIndexedHistory (NativeFrame)
open TypedForHeader (Fallthrough)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate} {administrative : Core.Context}
  {type : Ty} {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults entry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_prefix_bounded_for_with_return_reachable
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native) (ready : readiness.Ready context state)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReadyReturn protocol readiness context scope canonical finalContext tail.scope tail.canonical) ∧
      readiness.Ready finalContext tail.state ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after size with
  | @nil context scope code next =>
    cases trace
    exact ⟨⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩,
      .refl _, .refl _, .refl _ _, .refl _, protocol.refl state, ⟨ReadyReturn.refl protocol readiness _ _ canonical⟩, ready, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining _remainingErrors ih =>
    cases trace with | cons first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ gate) state read)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        have nextReady := transfers.absent state nextState ready extended allocated preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended allocated)
        obtain ⟨tail, maps, worlds, lastFrame, metadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        exact ⟨tail,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
          protocol.trans allocationRelated tailRelated,
          ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical payload
            (.cellRef (OptionalCell.cellType payload) (store.length + 2))) tailReturn⟩, tailReady, (ContinuationAgreement.letE allocationEval).trans agreement⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining _remainingErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
            environments heaps locals agrees actualTyped state ready (.value initialTrace)
        cases represented with
        | value payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ gate) middleState frameRead)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.initialized middleState nextState middlePost.1 extended
            (sourceType ▸ middlePost.2) allocated allocationFrame
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letInitialized initialTrace.sound mono extended allocated)
          obtain ⟨tail, finalMaps, finalWorlds, finalFrame, finalMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
            protocol.trans expressionRelated (protocol.trans allocationRelated tailRelated),
            ⟨ReadyReturn.then (ReadyReturn.binding stateBindings transfers extended scope canonical lowered.type
              (.cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2))) tailReturn⟩, tailReady, ?_⟩
          rw [sequence_rename]
          exact (ContinuationAgreement.bind initialEval).trans ((ContinuationAgreement.letE allocationEval).trans agreement)
      | letInitializedGeneralized captures poly other allocated => exact False.elim (poly mono)
  | @discard context scope expression expressionNode rest lowered body found child remaining _remainingErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
          boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
            environments heaps locals agrees actualTyped state ready (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
          obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middlePost.1 rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            protocol.trans expressionRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at agreement
          exact (ContinuationAgreement.bind first).trans agreement
  | @assign context scope assignment operator rhs rest body head remaining _remainingErrors _headErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentTransition, prefixAgreement⟩ :=
          assignments _ valid head (sites.assignment itemFact)
            environments heaps locals agrees actualTyped state ready assigned (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans assignmentRelated tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNot context scope assignment rest body head remaining _remainingErrors _headErrors ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence
            environments heaps locals agrees actualTyped assigned.sound
        let middleState := stateTransport.extend state maps worlds preservation metadata
        have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
        have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, tailRelated, ⟨tailReturn⟩, tailReady, agreement⟩ :=
          ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
          protocol.trans (stateTransport.related state maps worlds preservation metadata) tailRelated, ⟨tailReturn⟩, tailReady, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

end WithReady

include definitions registered producer acquire stateTransport stateBindings in
theorem Tree.preserves_prefix_bounded_for_with_return_reachable
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry) program evidence
      source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment finalEnvironment : Dynamic.Environment} {canonical actual : Environment}
    {before after : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (gate : condition contextLocation native)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      protocol.Relates state tail.state ∧
      Nonempty (ReturnTo protocol scope canonical tail.scope tail.canonical) ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  obtain ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo⟩, _ready, agreement⟩ :=
    WithReady.Tree.preserves_prefix_bounded_for_with_return_reachable (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol) (facts := fun _ _ => True) (itemFacts := fun _ _ => True)
      (exprFacts := fun _ _ _ => True) (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
      (sites := WithReady.StaticSites.trivial program evidence source)
      (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
      (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
      validity extend budget
      (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
        (certificates context) context administrative budget (assignments context valid))
      (fun context valid size within => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial
        protocol (boundedMeaning context valid size within))
      tree errors valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo.toReturnTo⟩, agreement⟩

end Stateful
end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader

namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Progress postValues postValues_typed postValues_agree post_rename)
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (guard : Location → CallableIndexedHistory.NativeFrame → Prop)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (producer : OrdinaryAllocation.Producer protocol layouts frameLayout
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (acquire : ∀ location native, guard location native → OrdinaryAllocation.ReadyAt producer location native)
  (stateTransport : AdministrativeTransport protocol) (stateBindings : Bindings protocol)
  {context : SourceSemantics.Context} {scope : Scope} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {type : Ty} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

namespace WithReady
open RecursiveNamedLexicalContracts.Stateful.WithReady
variable (readiness : Readiness protocol)
  (facts : SourceSemantics.Context → List ForItemForm → Prop)
  (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
  (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
  (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
  (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
  (sites : StaticSites facts itemFacts exprFacts assignmentFacts snapshotFacts program evidence source)
  (transfers : AllocationTransfers protocol readiness stateBindings source)

include definitions registered producer acquire stateTransport stateBindings sites transfers solved in
theorem post_preserves_bounded_for_reachable
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native) (ready : readiness.Ready context state.retained)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained ∧ readiness.Ready context reached.retained := by
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.live.selfTyped state.live.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩ :=
    Tree.preserves_prefix_bounded_for_with_return_reachable (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence)
      (protocol := protocol) (condition := guard) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
      (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts)
      (sites := sites) (transfers := transfers) (snapshots := snapshots)
      validity extend budget assignments boundedMeaning tree errors valid itemsFacts
      state.live.environments state.live.heaps state.live.locals (postValues_agree agrees type location continued)
      postTyped reference read state.live.contextUnmapped state.retained guarded ready trace bounded
  exact post_preserves_bounded_for_with_header_result protocol guard functions evidence readiness validity state continued
    ⟨tail, maps, worlds, preservation, metadata, related, ⟨returnTo⟩, tailReady, agreement⟩

end WithReady

include definitions registered producer acquire stateTransport stateBindings solved in
theorem post_preserves_bounded_for_reachable
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    {native : CallableIndexedHistory.NativeFrame}
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frameLayout native))
    (guarded : guard contextLocation native)
    (continued : Bool)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore ∧
      ∃ reached : ProtectedStateTransition.For.State protocol values registry functions context scope administrative actualContext frameLayout environment canonical actual
        contextLocation location type conditionCode body (postCode.rename ξ) selfReason finalMap finalWorld after finalStore,
        protocol.Relates state.retained reached.retained := by
  have result := WithReady.post_preserves_bounded_for_reachable
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence)
    (protocol := protocol) (guard := guard) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness.trivial protocol)
    (facts := fun _ _ => True) (itemFacts := fun _ _ => True) (exprFacts := fun _ _ _ => True)
    (assignmentFacts := fun _ _ _ _ => True) (snapshotFacts := fun _ _ => True)
    (sites := WithReady.StaticSites.trivial program evidence source)
    (transfers := RecursiveNamedLexicalContracts.Stateful.WithReady.AllocationTransfers.trivial protocol stateBindings source)
    (snapshots := WithReady.SnapshotTransfers.trivial protocol validity program evidence source)
    validity extend budget
    (fun context valid => WithReady.assignment_prefix_trivial protocol functions program evidence source
      (certificates context) context administrative budget (assignments context valid))
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.WithReady.ExpressionPreservesAt.of_true
      protocol program evidence (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      (certificates context) (boundedMeaning context valid size smaller))
    tree errors valid True.intro agrees reference state read guarded True.intro continued trace bounded
  obtain ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related, _ready⟩ := result
  exact ⟨finalStore, finalMap, finalWorld, evaluated, progress, reached, related⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
