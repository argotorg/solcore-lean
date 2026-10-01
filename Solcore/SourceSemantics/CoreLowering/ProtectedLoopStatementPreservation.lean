import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControl
import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape

/-! Actual lexical tree induction transports the guarded entry through source
allocations and hidden native slots. No canonical heap/environment typing is
used to manufacture installed code, captures or history. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open ProtectedLexicalStatements
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalWhile (FlowRep)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized sequence_rename allocate_absent allocate_initialized valid_extend)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressions : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {solved : List SolvedRequirement}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends values.registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

include definitions registered extension faithful observations transport bindings in
theorem Tree.preserves
    (expressionPreserves : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {administrative : Core.Context}
    (tree : Tree layouts owner active frame globals onError values source expressions administrative ambient.definitions registry faults
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    {outcome : Dynamic.ControlOutcome} {resultContext : SourceSemantics.Context}
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
    (trace : Executes mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  induction tree generalizing mapping world environment canonical actual before after store ξ actualContext contextLocation native outcome resultContext with
  | lexical fragment =>
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
      ProtectedLexicalAssignments.Tree.preserves functions definitions registered extension faithful observations program evidence transport bindings
        expressionPreserves fragment contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace
    exact ⟨value, finalStore, finalMap, finalWorld, completed, FlowRep.of_lexical represented,
      finalHeaps, maps, worlds, frame, metadata, lexical⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, allocated, tailTrace⟩ := source_view_absent unique found form mono extended trace
    obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation⟩ :=
      allocate_absent functions definitions registered mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical⟩ :=
      ih (valid_extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        (bindings.prepend (transport.extend installed ⟨_, rfl⟩ ⟨_, rfl⟩ preservation
          (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename]
    rcases source_view_initialized unique found form mono extended trace with ⟨reason, rfl, rfl, failed⟩ |
        ⟨sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata⟩ :=
        expressionPreserves _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata⟩ :=
        expressionPreserves _ contextValid initial initialFound
          environments heaps locals agrees actualTyped installed (.value initialTrace)
      cases represented with
      | value payload =>
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame⟩ :=
          allocate_initialized functions definitions registered mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical⟩ :=
          ih (valid_extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              (bindings.prepend (transport.extend
                (transport.extend installed maps worlds preservation metadata) ⟨_, rfl⟩ ⟨_, rfl⟩ allocationFrame
                (Dynamic.HeapMetadataExtend.of_allocation allocated))) tailTrace
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases TypedScopedStatements.discard_view unique (lookupStatement?_sound found) form guard trace with ⟨reason, rfl, rfl, failed⟩ | ⟨sourceValue, middle, childTrace, tail⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        expressionPreserves _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata⟩ :=
        expressionPreserves _ contextValid child expressionFound
          environments heaps locals agrees actualTyped installed (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩ :=
          ih contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            (transport.extend installed firstMaps firstWorlds firstFrame firstMetadata) tail
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | block found form inner remaining innerIH remainingIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.block_preserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.conditional_preserves transport unique expressionPreserves (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame) (globals := globals) found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace


  | @assignment context scope mode id node assignment operator rhs rest expected type body found form head headErrors remaining ih =>
    have go {middleContext : SourceSemantics.Context} {next : Dynamic.Environment} {middle : Dynamic.Heap}
        (first : Dynamic.StatementExecutes program context evidence source environment before id middleContext (.fallthrough next) middle)
        (tail : Executes mode program middleContext evidence source next middle rest resultContext outcome after) :
        ∃ value finalStore finalMap finalWorld,
          Evaluates actual store ((head.emit body (LocalLoop.controlType type)).rename ξ) value finalStore ∧
          FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
          LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
          AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
          LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
            context scope environment resultContext after := by
      obtain ⟨rfl, same, updated, assigned⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
      cases same
      obtain ⟨written, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata, count, typed, observed, continuation⟩ :=
        ProtectedAssignmentHeads.Head.preserves_prefix functions extension program evidence transport
          (expressionPreserves _ contextValid) faithful observations head
          environments heaps locals agrees actualTyped installed assigned
      have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, lastMaps, lastWorlds, lastFrame, lastMetadata, lexical⟩ :=
        ih contextValid (environments.extend maps worlds) middleHeaps (locals.mono metadata)
          (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference frameRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1 observed tail
      exact ⟨value, finalStore, finalMap, finalWorld,
        (continuation body (LocalLoop.controlType type)).wrap (by simpa only [DataPlaceChildExpressions.rename_prefix, count,
          SourceCoreDataPlaces.shift, SourceCoreCompatibleDataPlaces.shift] using completed),
        represented, finalHeaps, maps.trans lastMaps, worlds.trans lastWorlds, preservation.trans lastFrame, metadata.trans lastMetadata, lexical⟩
    cases source_view trace with
    | control executed =>
      rcases ScalarStatementViews.cons_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) executed with
        ⟨_, _, _, first, tail⟩ | ⟨first, terminal⟩
      · exact go first (by cases mode <;> exact .control tail)
      · obtain ⟨_, rfl, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form first
        cases terminal
    | fault failed =>
      rcases ScalarStatementViews.cons_fault_view mode unique (lookupStatement?_sound found) (by intro _ _; simp [form]) failed with
        ⟨rfl, first⟩ | ⟨_, _, _, first, tail⟩
      · obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, preservation, metadata, observed⟩ :=
          ProtectedAssignmentHeads.Head.preserves_fault functions extension program evidence transport
            (expressionPreserves _ contextValid) faithful observations head
            environments heaps locals agrees actualTyped installed headErrors
            (ScalarStatementViews.assignValue_fault unique (lookupStatement?_sound found) form first) body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          _, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩
      · exact go first (by cases mode <;> exact .fault tail)

  | @breaking context scope mode id node rest expected type found form =>
    obtain ⟨rfl, rfl, rfl⟩ := breaking_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.breaking] using LocalLoop.breaking_evaluates _ actual store,
      .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | @continuing context scope mode id node rest expected type found form =>
    obtain ⟨rfl, rfl, rfl⟩ := continuing_view unique found form trace
    exact ⟨_, store, mapping, world, by simpa only [LoopRenaming.continuing] using LocalLoop.continuing_evaluates _ actual store,
      .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _, _, _, _, .here, environments, locals⟩

  | whileLoop found form conditionFound conditionType conditionTree loopBody nativeTyped remaining loopIH restIH =>
    exact Control.sequence_preserves transport (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) found (by intro expression; simp [form])
      (Control.of_retained_preserves functions program evidence (ProtectedWhile.Body.while_preserves functions program evidence transport
        (expressionPreserves _ contextValid) found form conditionFound conditionTree nativeTyped unique loopIH)) restIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped installed trace

end Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatements
