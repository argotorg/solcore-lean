import Solcore.SourceSemantics.CoreLowering.ForHeaderNativeBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBitNotStatementContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderPreservation

/-! Completed native headers reconstruct their independent source prefix or
first fault. A successful prefix exposes the real remaining evaluation under
its actual typed environment; no source trace or child execution is assumed. -/
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
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    ProtectedExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
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

include definitions registered observations producer acquire stateTransport stateBindings in
theorem Tree.reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (assignments : ∀ context, validity context → AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults size))
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    ResultAtFor protocol condition validity size registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment ⟨scope, mapping, world, before, store, canonical⟩ state items value finalStore := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native value finalStore size with
  | @nil context scope code next =>
    exact .continues ⟨⟨scope, code, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, state, gate⟩ .nil (.refl _) (.refl _) (.refl _ _) (.refl _) (protocol.refl state) evaluated (Nat.le_refl _)
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
      TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append state ((acquire _ _ gate) state read)
    obtain ⟨nextState, allocationRelated⟩ := allocationTransition
    obtain ⟨remainingSize, smaller, remainingEval⟩ := ForHeaderNativeBounds.allocation_body evaluated allocationEval
    have reflected := ih (extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
      (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        nextState gate remainingEval (Nat.le_trans (Nat.le_of_lt smaller) bounded)
    exact reflected.prepend_binding stateBindings nextState allocationRelated (.letUninitialized mono extended .append)
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩)
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩)
      preservation (.of_allocation Dynamic.Heap.Allocates.append) (Nat.le_of_lt smaller)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    rw [sequence_rename] at evaluated
    have input : ∃ input middle childSize, childSize < size ∧ EvaluationSize childSize actual store (lowered.expression.rename ξ) input middle := by
      cases evaluated with
      | caseLeft initial branch | caseRight initial branch => exact ⟨_, _, _, by omega, initial⟩
    obtain ⟨input, middleStore, initialSize, initialSmaller, initialEval⟩ := input
    obtain ⟨sourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
      boundedReflection _ valid _ (Nat.lt_of_lt_of_le initialSmaller bounded) child found
        environments heaps locals agrees actualTyped state initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
        exact .fault (.head (.letInitializer mono failed)) rfl matched middleHeaps maps worlds preservation metadata expressionTransition
    | value payload =>
      obtain ⟨middleState, expressionRelated⟩ := expressionTransition
      cases initialTrace with | value initialTrace =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append middleState ((acquire _ _ gate) middleState frameRead)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        obtain ⟨remainingSize, smaller, tailEval⟩ := ForHeaderNativeBounds.initialized_body evaluated initialEval.sound allocationEval
        have reflected := ih (extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (List.getElem?_eq_some_iff.mp frameRead).1).1
          nextState gate tailEval (Nat.le_trans (Nat.le_of_lt smaller) bounded)
        exact reflected.prepend_binding stateBindings nextState (protocol.trans expressionRelated allocationRelated) (.letInitialized initialTrace mono extended .append)
          (maps.trans (show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩))
          (worlds.trans (show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩))
          (preservation.trans allocationFrame) (metadata.trans (.of_allocation Dynamic.Heap.Allocates.append)) (Nat.le_of_lt smaller)
  | @discard context scope expression expressionNode rest lowered body found child remaining remainingErrors ih =>
    rw [LoopRenaming.discard] at evaluated
    have complete := evaluated
    cases evaluated with
    | caseLeft childEvaluation branch =>
      obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
        boundedReflection _ valid _ (by omega) child found
          environments heaps locals agrees actualTyped state childEvaluation
      cases represented with | fault matched =>
        cases trace with | fault failed =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic complete.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact .fault (.head (.expression failed)) rfl matched finalHeaps maps worlds preservation metadata expressionTransition
    | caseRight childEvaluation branch =>
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, maps, worlds, preservation, metadata, expressionTransition⟩ :=
        boundedReflection _ valid _ (by omega) child found
          environments heaps locals agrees actualTyped state childEvaluation
      cases represented with | @value _ coreValue payload =>
        obtain ⟨middleState, expressionRelated⟩ := expressionTransition
        cases trace with | value childTrace =>
          have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (GenericExpressionMeaning.agree_prefix agrees _) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState gate
            (by simpa only [GenericExpressionMeaning.rename_prefix] using branch) (by omega)
          exact reflected.prepend middleState expressionRelated (.expression childTrace) maps worlds preservation metadata (by omega)
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    have assigned := assignments _ valid head
      environments heaps locals agrees actualTyped state headErrors evaluated bounded
    cases assigned with
    | fault trace same matched finalHeaps maps worlds preservation metadata assignmentTransition =>
      exact .fault (.head (.assignValue trace)) same matched finalHeaps maps worlds preservation metadata assignmentTransition
    | success trace middleHeaps maps worlds preservation metadata count typed assignmentTransition smaller remainingEval =>
      obtain ⟨middleState, assignmentRelated⟩ := assignmentTransition
      have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
        ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 middleState gate
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval) (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact reflected.prepend middleState assignmentRelated (.assignValue trace) maps worlds preservation metadata (Nat.le_of_lt smaller)

  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    rcases head.reflects_sized functions program evidence observations
      environments heaps locals agrees actualTyped headErrors evaluated with
      ⟨sourceSize, reason, token, after, finalMap, finalWorld, trace, rfl, matched, finalHeaps, maps, worlds, preservation, metadata⟩ |
      ⟨sourceSize, updated, middle, written, middleMap, middleWorld, slots, remainingSize, trace, middleHeaps, maps, worlds, preservation, metadata, count, typed, smaller, remainingEval⟩
    · exact .fault (.head (.assignBitNot trace)) rfl matched finalHeaps maps worlds preservation metadata
        ⟨stateTransport.extend state maps worlds preservation metadata, stateTransport.related state maps worlds preservation metadata⟩
    · let middleState := stateTransport.extend state maps worlds preservation metadata
      have reflected := ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
        ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        middleState gate
        (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using remainingEval) (Nat.le_trans (Nat.le_of_lt smaller) bounded)
      exact reflected.prepend middleState (stateTransport.related state maps worlds preservation metadata) (.assignBitNot trace) maps worlds preservation metadata (Nat.le_of_lt smaller)

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

include extension faithful observations transport in
private theorem legacyAssignmentReflection (context : SourceSemantics.Context) (budget : Nat)
    (boundedReflection : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry))
    (functionTypes : FunctionRuntimeViews functions) :
    Stateful.AssignmentReflectsAt (ProtectedStateTransition.Lexical.legacyProtocol entry) functions (registry := registry)
      program evidence source (certificates context) context administrative faults budget := by
  intro scope assignment operator rhs head mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed state errors next output value finalStore size evaluated within
  have result := ProtectedAssignmentHeads.Head.reflects_reachable_bounded functions extension program evidence transport faithful observations head
    environments heaps locals agrees typed state.down budget boundedReflection functionTypes errors evaluated within
  cases result with
  | fault trace same matched finalHeaps maps worlds preservation metadata installed =>
    exact .fault trace same matched finalHeaps maps worlds preservation metadata ⟨⟨installed⟩, trivial⟩
  | success trace finalHeaps maps worlds preservation metadata count typed installed smaller remaining =>
    exact .success trace finalHeaps maps worlds preservation metadata count typed ⟨⟨installed⟩, trivial⟩ smaller remaining

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_reachable_bounded_for
    (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context next : SourceSemantics.Context} {binder : TypedBinder},
      validity context → BinderExtends source.owner context binder next → validity next) (budget : Nat)
    (boundedReflection : ∀ context, validity context →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAtFor validity size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  have result := Stateful.Tree.reflects_reachable_bounded_for
    (solved := solved) (functions := functions) (definitions := definitions) (registered := registered)
    (program := program) (evidence := evidence) (observations := observations)
    (protocol := ProtectedStateTransition.Lexical.legacyProtocol entry) (condition := fun _ _ => True)
    (producer := legacyProducer functions transport bindings)
    (acquire := fun location native _ => ProtectedStateTransition.OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
    (stateTransport := ProtectedStateTransition.Lexical.legacyTransport transport) (stateBindings := legacyBindings bindings)
    validity extend budget
    (fun context valid => legacyAssignmentReflection functions extension program evidence transport faithful observations context budget (boundedReflection context valid) functionTypes)
    (fun context valid size smaller => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
      functions program evidence transport (boundedReflection context valid size smaller))
    tree errors valid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated bounded
  exact result.toLegacy

include definitions registered extension faithful observations transport bindings in
theorem Tree.reflects_reachable_bounded (budget : Nat)
    (boundedReflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.ReflectsAt size
        (CompatibleAmbientHeap.payloadModel values.checked registry functions) program context evidence source (certificates context) faults entry)) (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    {size : Nat} (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedHeaderContracts.ResultAt size (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable_bounded_for (functions := functions) (tree := tree)
    (validity := fun context => CompatibleExpressionLiterals.ContextValid solved context evidence)
    (extend := fun valid extended => TypedLexicalControl.valid_extend valid extended)
  all_goals assumption

include definitions registered extension meaning reflection faithful observations transport bindings in
theorem Tree.reflects_reachable (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.ReachableErrors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore  := by
  have _legacyMeaning := @meaning
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  exact (tree.reflects_reachable_bounded functions definitions registered extension program evidence transport bindings faithful observations size
    (fun context valid => RecursiveNamedBoundedContracts.reflects_below_of_unbounded (reflection context valid) size)
    functionTypes errors valid environments heaps locals agrees actualTyped reference read unmapped installed sized (Nat.le_refl size)).erase

include definitions registered extension meaning reflection faithful observations transport bindings in
/-- Original API, interpreted through the reachable diagnostic receipt. -/
theorem Tree.reflects (functionTypes : FunctionRuntimeViews functions)
    {context : SourceSemantics.Context} {scope : Scope} {items : List ForItemForm} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative type continuation
      context scope items code) (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {value : Value}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    (evaluated : Evaluates actual store (code.rename ξ) value finalStore) :
    Result (entry := entry) registry functions program source solved evidence administrative frame globals contextLocation native type faults continuation
      context environment before items mapping world store value finalStore := by
  apply Tree.reflects_reachable (functions := functions) (tree := tree) (errors := errors.reachable)
  all_goals assumption

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader
