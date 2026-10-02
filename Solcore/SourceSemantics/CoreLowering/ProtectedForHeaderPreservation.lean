import Solcore.SourceSemantics.CoreLowering.ProtectedForHeaderControl

/-! Successful ordinary header prefixes retain their real stopping scope and
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
      ContinuationAgreement actual store (code.rename ξ) tail.actual tail.store (tail.code.rename tail.embedding) := by
  induction tree generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext finalEnvironment after with
  | nil next =>
    cases trace
    exact ⟨⟨⟨_, _, mapping, world, canonical, actual, actualContext, ξ, store, next, valid,
      environments, heaps, locals, agrees, actualTyped, reference, read, unmapped⟩, installed⟩,
      .refl _, .refl _, .refl _ _, .refl _, .refl _ _ _⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining ih =>
    cases trace with | cons first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
          allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated
        obtain ⟨tail, maps, worlds, lastFrame, metadata, agreement⟩ :=
          ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
              (Dynamic.HeapMetadataExtend.of_allocation allocated))) rest
        exact ⟨tail,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
          (ContinuationAgreement.letE allocationEval).trans agreement⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining ih =>
    cases trace with | cons first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.value initialTrace)
        cases represented with
        | value payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
            allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
          obtain ⟨tail, finalMaps, finalWorlds, finalFrame, finalMetadata, agreement⟩ :=
            ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation allocated))) rest
          refine ⟨tail,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), ?_⟩
          rw [sequence_rename]
          exact (ContinuationAgreement.bind initialEval).trans ((ContinuationAgreement.letE allocationEval).trans agreement)
      | letInitializedGeneralized captures poly other allocated => exact False.elim (poly mono)
  | discard found child remaining ih =>
    cases trace with | cons first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
            ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed maps worlds preservation metadata) rest
          refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
          rw [LoopRenaming.discard]
          rw [GenericExpressionMeaning.rename_prefix] at agreement
          exact (ContinuationAgreement.bind first).trans agreement
  | @assign context scope assignment operator rhs rest body head remaining ih =>
    cases trace with | cons first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, nextInstalled, prefixAgreement⟩ :=
          ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence transport (meaning _ valid) faithful observations head
            environments heaps locals agrees actualTyped installed assigned
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 nextInstalled rest
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

  | @bitNot context scope assignment rest body head remaining ih =>
    cases trace with | cons first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence observations
            environments heaps locals agrees actualTyped assigned
        obtain ⟨tail, lastMaps, lastWorlds, lastFrame, lastMetadata, agreement⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed maps worlds preservation metadata) rest
        refine ⟨tail, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, ?_⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).trans (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using agreement)

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
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  induction errors generalizing mapping world actualContext environment canonical actual before store ξ contextLocation native finalContext after with
  | nil => cases trace
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same remaining remainingErrors ih =>
    cases trace with
    | head failed => cases failed with | polymorphicLet poly unsupported => exact False.elim (poly mono)
    | tail first rest =>
      cases first with | letUninitialized _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
          allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
            environments heaps locals agrees actualTyped reference read allocated
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, maps, worlds, lastFrame, metadata⟩ :=
          ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
              (Dynamic.HeapMetadataExtend.of_allocation allocated))) rest
        exact ⟨token, finalStore, finalMap, finalWorld, .letE allocationEval completed, matched, finalHeaps,
          (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
          (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
          preservation.trans lastFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata⟩
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same remaining remainingErrors ih =>
    rw [sequence_rename]
    cases trace with
    | head failed =>
      cases failed with
      | polymorphicLet poly unsupported => exact False.elim (poly mono)
      | letInitializer _ failed =>
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.fault failed)
        cases represented with | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩
    | tail first rest =>
      cases first with
      | letInitialized initialTrace _ other allocated =>
        cases binder_context_eq extended other
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.value initialTrace)
        cases represented with
        | value payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
            allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
            ih (valid_extend valid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation allocated))) rest
          exact ⟨token, finalStore, finalMap, finalWorld, LanguageResult.bind_success _ initialEval (.letE allocationEval completed), matched, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata)⟩
      | letInitializedGeneralized captures poly other allocated => exact False.elim (poly mono)
  | @discard context scope expression expressionNode rest lowered body found child remaining remainingErrors ih =>
    rw [LoopRenaming.discard]
    cases trace with
    | head failed =>
      cases failed with | expression failed =>
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.fault failed)
        cases represented with | fault matched =>
          exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩
    | tail first rest =>
      cases first with | expression childTrace =>
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
          meaning _ valid child found
            environments heaps locals agrees actualTyped installed (.value childTrace)
        cases represented with
        | @value _ coreValue payload =>
          obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
            ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue) (.cons payload.runtime_hasType (actualTyped.weaken worlds)) reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed maps worlds preservation metadata) rest
          refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
          rw [GenericExpressionMeaning.rename_prefix] at completed
          exact LocalSequence.discard_success _ first completed
  | @assign context scope assignment operator rhs rest body head remaining remainingErrors headErrors ih =>
    cases trace with
    | head failed =>
      cases failed with | assignValue failed =>
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, _⟩ :=
          ProtectedAssignmentHeads.Head.preserves_fault_reachable functions extension program evidence transport (meaning _ valid) faithful observations head
            environments heaps locals agrees actualTyped installed headErrors failed body (LocalLoop.controlType type)
        exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata⟩
    | tail first rest =>
      cases first with | assignValue assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, nextInstalled, prefixAgreement⟩ :=
          ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence transport (meaning _ valid) faithful observations head
            environments heaps locals agrees actualTyped installed assigned
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 nextInstalled rest
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

  | @bitNot context scope assignment rest body head remaining remainingErrors headErrors ih =>
    cases trace with
    | head failed =>
      cases failed with | assignBitNot failed =>
        exact head.preserves_fault functions program evidence observations
          environments heaps locals agrees headErrors failed body (LocalLoop.controlType type)
    | tail first rest =>
      cases first with | assignBitNot assigned =>
        obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, prefixAgreement⟩ :=
          head.preserves_prefix functions program evidence observations
            environments heaps locals agrees actualTyped assigned
        obtain ⟨token, finalStore, finalMap, finalWorld, completed, matched, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata⟩ :=
          ih valid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              (transport.extend installed maps worlds preservation metadata) rest
        refine ⟨token, finalStore, finalMap, finalWorld, ?_, matched, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata⟩
        exact (prefixAgreement body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed)

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
