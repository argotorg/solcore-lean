import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderAssignmentPayloadContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateWhileReady
import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderControl

/-! Header prefixes retain their real stopping scope and
actual installed observations through marked allocations and seven-slot writes.
The continuation agreement concerns the real reached prefix; its execution is
not a premise of the static tree. -/
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

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_prefix_bounded_for_with_return
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
  induction tree generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after size with
  | nil next =>
    cases trace
    exact ⟨⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩,
      .refl _, .refl _, .refl _ _, .refl _, protocol.refl state, ⟨ReadyReturn.refl protocol readiness _ _ canonical⟩, ready, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining ih =>
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
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining ih =>
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
  | discard found child remaining ih =>
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
  | @assign context scope assignment operator rhs rest body head remaining ih =>
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

  | @bitNot context scope assignment rest body head remaining ih =>
    have itemFact := sites.head itemsFacts
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence observations
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

include definitions registered observations producer acquire stateTransport stateBindings in
theorem Tree.preserves_prefix_bounded_for_with_return
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
    WithReady.Tree.preserves_prefix_bounded_for_with_return (solved := solved)
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
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
      tree valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨tail, maps, worlds, frame, metadata, related, ⟨returnTo.toReturnTo⟩, agreement⟩

include definitions registered observations producer acquire stateTransport stateBindings in
theorem Tree.preserves_prefix_bounded_for
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
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  obtain ⟨tail, maps, worlds, preservation, metadata, related, _returnTo, agreement⟩ :=
    Tree.preserves_prefix_bounded_for_with_return
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
      (stateTransport := stateTransport) (stateBindings := stateBindings)
      validity extend budget assignments boundedMeaning tree valid environments heaps locals agrees actualTyped
      reference read unmapped state gate trace bounded
  exact ⟨tail, maps, worlds, preservation, metadata, related, agreement⟩

end Stateful

private def legacyBindings (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.Bindings (ProtectedStateTransition.Lexical.legacyProtocol entry) where
  prepend state _id _type _value := ⟨bindings.prepend state.down⟩
  prepend_related _state _id _type _value := trivial
  prepend_records _state _id _type _value := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _state := trivial
  restore_records _state := rfl

private def legacyProducer (functions : FunctionModel values.checked.catalog ambient)
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    ProtectedStateTransition.OrdinaryAllocation.Producer (ProtectedStateTransition.Lexical.legacyProtocol entry) layouts frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) :=
  ProtectedStateTransition.OrdinaryAllocation.of_administrative _
    (ProtectedStateTransition.Lexical.legacyTransport transport) (legacyBindings bindings)
    layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions)

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_prefix_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
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
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : TailFor validity (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  have assignments : ∀ context, validity context → Stateful.AssignmentPrefixPreservesAt
      (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry) program evidence source
      (certificates context) context administrative budget := by
    intro context valid scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
      environments heaps locals agrees typed state updated after size assigned within
    obtain ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed, installed, agreement⟩ :=
      ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport faithful observations head
        environments heaps locals agrees typed state.down budget (boundedMeaning _ valid) assigned within
    exact ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed,
      ⟨⟨installed⟩, trivial⟩, agreement⟩
  obtain ⟨tail, maps, worlds, preservation, metadata, _related, agreement⟩ :=
    Stateful.Tree.preserves_prefix_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      (producer := legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
      validity extend budget assignments
      (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (boundedMeaning context valid size smaller))
      tree valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace bounded
  exact ⟨tail.toLegacy, maps, worlds, preservation, metadata, agreement⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_prefix_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
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
    (installed : entry scope mapping world before store canonical)
    {size : Nat} (trace : SourceExecutionSize.ForItemsExecute program size context evidence source environment before items finalContext finalEnvironment after) (bounded : size ≤ budget) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  apply Tree.preserves_prefix_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem Tree.preserves_prefix {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
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
    (installed : entry scope mapping world before store canonical)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ tail : Tail (entry := entry) registry functions source solved evidence administrative frame globals contextLocation native continuation finalContext finalEnvironment after,
      LocationMap.Extends mapping tail.mapping ∧ WorldExtends world tail.world ∧
      AdministrativePreserved mapping store tail.mapping tail.store ∧ Dynamic.HeapMetadataExtend before after ∧
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding)  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsExecute.has_size trace
  exact tree.preserves_prefix_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)

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

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (AP : GenericForHeader.Structural.AssignmentPayload values source certificates administrative ambient.definitions)
    (UP : GenericForHeader.Structural.UnaryPayload)
    (unaryErrors : ∀ {context scope assignment} (head : CompatibleBitNotStatements.Head context scope assignment),
      UP head → head.Errors faults)
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesWithPayloadAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget (fun head => AP head))
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (eliminator : GenericForHeader.Structural.Eliminates
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (certificates := certificates)
      (definitions := ambient.definitions) (administrative := administrative) (type := type)
      (continuation := continuation) AP UP context scope items code)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  let M : SourceSemantics.Context → Scope → List ForItemForm → Expr → Prop :=
    fun context scope items code =>
    ∀ {finalContext : SourceSemantics.Context},
    ∀ (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget),
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩
  have algebra : GenericForHeader.Structural.BranchAlgebra
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (type := type) (continuation := continuation) AP UP M := by
    clear eliminator ready gate state unmapped read reference actualTyped agrees locals heaps environments
      bounded trace itemsFacts valid
    clear finalContext reason after size mapping world actualContext environment canonical actual before store ξ contextLocation native
      context scope items code
    constructor
    · intro context scope code next
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      cases trace
    · intro context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      cases trace with
      | head failed => cases failed with | polymorphicLet poly unsupported => exact False.elim (poly mono)
      | tail first rest =>
        cases first with | letUninitialized _ other allocated =>
          cases binder_context_eq extended other
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
            TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
              environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ gate) state read)
          obtain ⟨nextState, allocationRelated⟩ := allocationTransition
          have nextReady := transfers.absent state nextState ready extended allocated preservation
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.letUninitialized mono extended allocated)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, maps, worlds, lastFrame, metadata, tailTransition⟩ :=
            ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨tailState, tailRelated, tailPost⟩ := tailTransition
          let reached := stateBindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) tailState
          have restoredRelated := stateBindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) tailState
          have restoredPost := transfers.restore_fault (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (binder := binder) (type := payload) tailState tailPost
          exact ⟨token, finalStore, finalMap, finalWorld, .letE allocationEval completed, matched, finalHeaps,
            (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
            (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
            preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, ⟨reached, protocol.trans allocationRelated (protocol.trans tailRelated restoredRelated), restoredPost⟩⟩
    · intro context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      rw [sequence_rename]
      cases trace with
      | head failed =>
        cases failed with
        | polymorphicLet poly unsupported => exact False.elim (poly mono)
        | letInitializer _ failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact (.initialized mono) found)
              environments heaps locals agrees actualTyped state ready (.fault failed)
          cases represented with | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩
      | tail first rest =>
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
            obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailTransition⟩ :=
              ih (extend valid extended) nextFacts nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
                (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1
                nextState gate nextReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
            obtain ⟨tailState, tailRelated, tailPost⟩ := tailTransition
            let reached := stateBindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type) tailState
            have restoredRelated := stateBindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type) tailState
            have restoredPost := transfers.restore_fault (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (binder := binder) (type := lowered.type) tailState tailPost
            exact ⟨token, finalStore, finalMap, finalWorld, LanguageResult.bind_success _ initialEval (.letE allocationEval completed), matched, finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              ⟨reached, protocol.trans expressionRelated (protocol.trans allocationRelated (protocol.trans tailRelated restoredRelated)), restoredPost⟩⟩
        | letInitializedGeneralized captures poly other allocated => exact False.elim (poly mono)
    · intro context scope expression expressionNode rest lowered body found child ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      rw [LoopRenaming.discard]
      cases trace with
      | head failed =>
        cases failed with | expression failed =>
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
              environments heaps locals agrees actualTyped state ready (.fault failed)
          cases represented with | fault matched =>
            exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩
      | tail first rest =>
        cases first with | expression childTrace =>
          obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
            boundedMeaning _ valid _ (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) child found (sites.expression itemFact .discard found)
              environments heaps locals agrees actualTyped state ready (.value childTrace)
          cases represented with
          | @value _ coreValue payload =>
            obtain ⟨middleState, expressionRelated, middlePost⟩ := expressionTransition
            have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.expression childTrace.sound)
            obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
              ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState gate middlePost.1 rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
            obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
            refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
              ⟨reached, protocol.trans expressionRelated tailRelated, tailPost⟩⟩
            rw [GenericExpressionMeaning.rename_prefix] at completed
            exact LocalSequence.discard_success _ first completed
    · intro context scope assignment operator rhs rest body head headPayload ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have itemFact := sites.head itemsFacts
      cases trace with
      | head failed =>
        cases failed with | assignValue failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, assignmentTransition⟩ :=
            assignmentFaults _ valid head (sites.assignment itemFact)
              environments heaps locals agrees actualTyped state ready headPayload failed (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) body (LocalLoop.controlType type)
          exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, assignmentTransition⟩
      | tail first rest =>
        cases first with | assignValue assigned =>
          obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, assignmentTransition, prefixAgreement⟩ :=
            assignments _ valid head (sites.assignment itemFact)
              environments heaps locals agrees actualTyped state ready assigned (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨middleState, assignmentRelated, middleReady⟩ := assignmentTransition
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignValue assigned.sound)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            ⟨reached, protocol.trans assignmentRelated tailRelated, tailPost⟩⟩
          exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

    · intro context scope assignment rest body head headPayload ih
      intro finalContext valid itemsFacts mapping world actualContext environment canonical actual before after store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped state gate ready reason size trace bounded
      have headErrors := unaryErrors head headPayload
      have itemFact := sites.head itemsFacts
      cases trace with
      | head failed =>
        cases failed with | assignBitNot failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩ :=
            head.preserves_fault functions program evidence observations
              environments heaps locals agrees headErrors failed.sound body (LocalLoop.controlType type)
          exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
            ⟨stateTransport.extend state maps worlds preservation metadata, stateTransport.related state maps worlds preservation metadata,
              readiness.fault_after state (stateTransport.extend state maps worlds preservation metadata) (readiness.ready_fault ready) preservation⟩⟩
      | tail first rest =>
        cases first with | assignBitNot assigned =>
          obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
            head.preserves_prefix functions program evidence observations
              environments heaps locals agrees actualTyped assigned.sound
          let middleState := stateTransport.extend state maps worlds preservation metadata
          have middleReady := snapshots.ready state middleState ready valid (sites.snapshot itemFact) assigned.sound locals preservation
          have nextFacts := sites.tail (environment := environment) itemsFacts (Dynamic.ForItemExecutes.assignBitNot assigned.sound)
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, tailTransition⟩ :=
            ih valid nextFacts (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState gate middleReady rest (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          obtain ⟨reached, tailRelated, tailPost⟩ := tailTransition
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata,
            ⟨reached, protocol.trans (stateTransport.related state maps worlds preservation metadata) tailRelated, tailPost⟩⟩
          exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
            simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)
  exact eliminator M algebra valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

include definitions registered observations producer acquire stateTransport stateBindings sites transfers in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (snapshots : SnapshotTransfers protocol readiness validity snapshotFacts program evidence source)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol readiness assignmentFacts functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ExpressionPreservesAt protocol readiness program evidence
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) exprFacts (certificates context)
        (source := source) (context := context) (faults := faults) size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context) (itemsFacts : facts context items)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (gate : condition contextLocation native) (ready : readiness.Ready context state) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact Tree.preserves_fault_reachable_bounded_for_with_eliminator
    (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (observations := observations)
    (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
    (stateTransport := stateTransport) (stateBindings := stateBindings)
    (readiness := readiness) (facts := facts) (itemFacts := itemFacts) (exprFacts := exprFacts)
    (assignmentFacts := assignmentFacts) (snapshotFacts := snapshotFacts) (sites := sites) (transfers := transfers)
    (fun head => head.ReachableErrors registry faults) (fun head => head.Errors faults) (fun _ receipt => receipt)
    validity snapshots extend budget assignments assignmentFaults boundedMeaning
    (GenericForHeader.Structural.of_reachable_errors errors)
    valid itemsFacts environments heaps locals agrees actualTyped reference read unmapped state gate ready trace bounded

end WithReady

include definitions registered observations producer acquire stateTransport stateBindings in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative budget)
    (assignmentFaults : ∀ context, validity context → AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (gate : condition contextLocation native) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    WithReady.Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := protocol) (condition := condition) (producer := producer) (acquire := acquire)
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
      (fun context valid => WithReady.assignment_fault_trivial protocol functions program evidence source
        (certificates context) context administrative faults budget (assignmentFaults context valid))
      (fun context valid size within => ProtectedWhile.Body.Stateful.WithReady.expression_preserves_trivial
        protocol (boundedMeaning context valid size within))
      tree errors valid True.intro environments heaps locals agrees actualTyped reference read unmapped state gate True.intro trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

end Stateful

include extension faithful observations transport in
private theorem legacyAssignmentPrefix (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    Stateful.AssignmentPrefixPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state updated after size assigned within
  obtain ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed, installed, agreement⟩ :=
    ProtectedAssignmentHeads.Head.preserves_prefix_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning assigned within
  exact ⟨written, nextMap, nextWorld, slots, nextHeaps, maps, worlds, preservation, metadata, count, typed,
    ⟨⟨installed⟩, trivial⟩, agreement⟩

include extension faithful observations transport in
private theorem legacyAssignmentFault (context : SourceSemantics.Context) (budget : Nat)
    (boundedMeaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) :
    Stateful.AssignmentFaultPreservesAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors reason after size failed within next output
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, installed⟩ :=
    ProtectedAssignmentHeads.Head.preserves_fault_reachable_bounded functions extension program evidence transport faithful observations head
      environments heaps locals agrees typed state.down budget boundedMeaning errors failed within next output
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata,
    ⟨⟨installed⟩, trivial⟩⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_fault_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedMeaning : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, _transition⟩ :=
    Stateful.Tree.preserves_fault_reachable_bounded_for
      (functions := functions) (definitions := definitions) (registered := registered)
      (program := program) (evidence := evidence) (observations := observations)
      (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
      (producer := legacyProducer functions transport bindings)
      (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
      validity extend budget
      (fun context valid => legacyAssignmentPrefix functions extension program evidence transport faithful observations context budget (boundedMeaning context valid))
      (fun context valid => legacyAssignmentFault functions extension program evidence transport faithful observations context budget (boundedMeaning context valid))
      (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (boundedMeaning context valid size smaller))
      tree errors valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves_fault_reachable_bounded (budget : Nat)
    (boundedMeaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.ForItemsFault program size context evidence source environment before items finalContext reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning faithful observations transport bindings in
theorem Tree.preserves_fault_reachable {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after  := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ForItemsFault.has_size trace
  exact tree.preserves_fault_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.preserves_below_of_unbounded (meaning context valid) size)
    errors valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)

include definitions registered extension meaning faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.preserves_fault {context finalContext : SourceSemantics.Context} {scope : Scope}
    {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
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
    (installed : entry scope mapping world before store canonical) {reason : Dynamic.SemanticFault}
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  apply Tree.preserves_fault_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
