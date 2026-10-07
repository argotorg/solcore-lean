import Solcore.SourceSemantics.CoreLowering.ProtectedStateAllocationReadiness
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeSourceBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalControlBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedLexicalStatementReflection

/-! The existing two lexical Tree inductions carry the actual protected state
through expression children, marked allocation, and lexical tails. Each result
keeps three-way flow and stopping lexical evidence, with its state normalized
to the entry scope and canonical environment. A static physical-frame receipt
supplies allocation readiness from each reached state's real live read.
Legacy callers use the same proofs through guarded PLift witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open TypedScopedStatements (Executes FlowRep not_tail head_fault terminal_intro prepend source_view)
open TypedLexicalControl (LexicalResult source_view_absent source_view_initialized sequence_rename allocate_absent allocate_initialized valid_extend)
open GenericLexicalStatements (Tree Scope ValuesContext)
open RecursiveNamedLoopContracts (ExecutesAt)
open ProtectedLexicalStatements (return_unit_view nil_executes)

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
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
  (bindings : ProtectedExpressionMeaning.Binds entry)

namespace Stateful
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (condition : Location → NativeFrame → Prop)
  (producer : OrdinaryAllocation.Producer protocol layouts frame
    (CompatibleAmbientHeap.payloadModel values.checked registry functions))
  (stateBindings : Bindings protocol)
  (acquire : ∀ location native, condition location native → OrdinaryAllocation.ReadyAt producer location native)

include definitions registered producer stateBindings acquire in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  induction tree generalizing size mapping world administrative environment canonical actual before after store ξ actualContext contextLocation native outcome resultContext with
  | @nil context scope mode expected type allowed =>
    cases source_view trace.sound with
    | control executed =>
      obtain ⟨rfl, rfl, rfl⟩ := ScalarStatementViews.nil_view mode executed
      exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates _ _ _, .fallthrough environment,
        heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, Transition.refl protocol state⟩
    | fault failed => exact False.elim (ScalarStatementViews.nil_cannot_fault mode failed)
  | @returnUnit context scope mode id node rest found form =>
    obtain ⟨rfl, rfl, rfl⟩ := return_unit_view unique (lookupStatement?_sound found) form trace.sound
    exact ⟨_, store, mapping, world, LocalLoop.returned_evaluates .unit, .returned .unit,
      heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, Transition.refl protocol state⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, smaller⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.returning unique found form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
      expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
        environments heaps locals agrees actualTyped state childTrace
    cases represented with
    | value payload =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    | fault matched =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
    obtain ⟨rfl, childSize, expressionOutcome, childTrace, rfl, smaller⟩ :=
      RecursiveNamedStatementSourceBounds.tail_inv unique (lookupStatement?_sound found) form trace
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
      expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
        environments heaps locals agrees actualTyped state childTrace
    cases represented with
    | value payload =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
        .returned (valueType ▸ payload), finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    | fault matched =>
      exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
        .fault matched, finalHeaps, maps, worlds, frame, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨location, middle, tailSize, allocated, tailTrace, smaller⟩ :=
      RecursiveNamedLexicalTreeSourceBounds.absent unique found form mono extended trace
    obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
      TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read allocated state ((acquire _ _ conditioned) state read)
    obtain ⟨nextState, allocationRelated⟩ := allocationTransition
    obtain ⟨value, finalStore, finalMap, finalWorld, completed, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, tailTransition⟩ :=
      ih _ (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        nextState conditioned tailTrace
    obtain ⟨finalState, tailRelated⟩ := stateBindings.restore_reached
      (reached := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) nextState tailTransition
    exact ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval completed, represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated tailRelated⟩⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename]
    rcases RecursiveNamedLexicalTreeSourceBounds.initialized unique found form mono extended trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, location, middle, allocatedHeap, initialTrace, allocated, tailTrace, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid initial initialFound
          environments heaps locals agrees actualTyped state (.fault failed)
      cases represented with
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented, middleHeaps, maps, worlds, preservation, metadata, transition⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid initial initialFound
          environments heaps locals agrees actualTyped state (.value initialTrace)
      cases represented with
      | value payload =>
        obtain ⟨middleState, expressionRelated⟩ := transition
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        obtain ⟨result, finalStore, finalMap, finalWorld, completed, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailTransition⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) (extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState conditioned tailTrace
        obtain ⟨finalState, tailRelated⟩ := stateBindings.restore_reached
          (reached := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) nextState tailTransition
        exact ⟨result, finalStore, finalMap, finalWorld,
          LanguageResult.bind_success _ initialEval (.letE allocationEval completed), related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata), lexical.bind extended,
          ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated tailRelated)⟩⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rcases RecursiveNamedLexicalTreeSourceBounds.discard unique found form guard trace with
      ⟨childSize, reason, rfl, rfl, failed, smaller⟩ |
      ⟨childSize, tailSize, sourceValue, middle, childTrace, tail, smaller, tailSmaller⟩
    · obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, transition⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
          environments heaps locals agrees actualTyped state (.fault failed)
      cases represented with
      | fault matched =>
        exact ⟨_, finalStore, finalMap, finalWorld, by rw [LoopRenaming.discard]; exact LocalSequence.discard_failure _ evaluated,
          .fault matched, finalHeaps, maps, worlds, frame, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    · obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, transition⟩ :=
        expressionPreserves childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
          environments heaps locals agrees actualTyped state (.value childTrace)
      cases represented with
      | @value _ coreValue payload =>
        obtain ⟨middleState, expressionRelated⟩ := transition
        obtain ⟨value, finalStore, finalMap, finalWorld, second, represented, finalHeaps, maps, worlds, frame, metadata, lexical, tailTransition⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned tail
        obtain ⟨finalState, tailRelated⟩ := tailTransition
        refine ⟨value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame, firstMetadata.trans metadata, lexical, ⟨finalState, protocol.trans expressionRelated tailRelated⟩⟩
        rw [LoopRenaming.discard]
        rw [GenericExpressionMeaning.rename_prefix] at second
        exact LocalSequence.discard_success _ first second

  | block found form inner remaining innerIH remainingIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.sequence_preserves_at_for (validity := validity)
      (protocol := protocol) (condition := condition)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.block_preserves_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
        (globals := globals) (unique := unique) budget child within found form innerIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.sequence_preserves_at_for (validity := validity)
      (protocol := protocol) (condition := condition)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := unique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.conditional_preserves_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget child within unique expressionPreserves
        found form conditionFound conditionType conditionTree thenIH elseIH) remainingIH
      contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned trace

  | terminalBlock exactUnique found form inner stops issued innerIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.sequence_stopped_preserves_at_for (validity := validity)
      (protocol := protocol) (condition := condition)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := exactUnique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.block_preserves_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
        (globals := globals) (unique := exactUnique) budget child within found form innerIH)
      (GenericLexicalStatements.block_terminates exactUnique found form stops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned trace
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    exact RecursiveNamedLexicalControlBounds.Stateful.sequence_stopped_preserves_at_for (validity := validity)
      (protocol := protocol) (condition := condition)
      (functions := functions) (program := program) (evidence := evidence)
      (frameLayout := frame) (globals := globals) (unique := exactUnique) budget size bounded found (by intro expression; simp [form])
      (fun child within => RecursiveNamedLexicalControlBounds.Stateful.conditional_preserves_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget child within exactUnique expressionPreserves
        found form conditionFound conditionType conditionTree thenIH elseIH)
      (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
      contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned trace

include definitions registered producer stateBindings acquire in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
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
    (conditioned : condition contextLocation native)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  suffices result : ∃ resultContext outcome after finalMap finalWorld,
      Executes mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ by
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, preservation, metadata, lexical, transition⟩ := result
    obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
    exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, represented,
      finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩

  induction tree generalizing size mapping world administrative environment canonical actual before store ξ actualContext contextLocation native finalStore value with
  | @nil context scope mode expected type allowed =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.fallthrough_evaluates type actual store)
    exact ⟨context, _, before, mapping, world, nil_executes mode program context evidence source environment before, .fallthrough environment, heaps,
      .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, Transition.refl protocol state⟩
  | @returnUnit context scope mode id node rest found form =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
    exact ⟨context, _, before, mapping, world,
      terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnUnit (lookupStatement?_sound found) form) (.returned _),
      .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _, ⟨_, _, _, .here, environments, locals⟩, Transition.refl protocol state⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
        environments heaps locals agrees actualTyped state childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, head_fault mode rest (.returnValue (lookupStatement?_sound found) form failed.sound),
          .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    | value payload =>
      cases trace with | value childTrace =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, terminal_intro mode rest (lookupStatement?_sound found) (by intro expression; simp [form]) (.returnValue (lookupStatement?_sound found) form childTrace.sound) (.returned _),
          .returned (valueType ▸ payload), finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
    rw [LoopRenaming.returnValue] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, preservation, metadata, transition⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
        environments heaps locals agrees actualTyped state childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_failure _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, .fault (.tailExpression (lookupStatement?_sound found) form failed.sound),
          .fault matched, finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    | value payload =>
      cases trace with | value childTrace =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalLoop.returnValue_success _ childEvaluation.sound)
        exact ⟨context, _, after, finalMap, finalWorld, .control (.tailExpression (lookupStatement?_sound found) form childTrace.sound),
          .returned (valueType ▸ payload), finalHeaps, maps, worlds, preservation, metadata,
          ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
    obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, preservation, allocationTransition⟩ :=
      TypedLexicalControl.Stateful.allocate_absent functions definitions registered protocol producer mono extended ordinary projected allocation annotation same
        environments heaps locals agrees actualTyped reference read Dynamic.Heap.Allocates.append state ((acquire _ _ conditioned) state read)
    obtain ⟨nextState, allocationRelated⟩ := allocationTransition
    obtain ⟨tailSize, smaller, continuation⟩ := evaluated.let_body allocationEval
    obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, finalFrame, metadata, lexical, transition⟩ :=
      ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) (extend contextValid extended) nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
        (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        nextState conditioned continuation
    obtain ⟨finalState, tailRelated⟩ := stateBindings.restore_reached
      (reached := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
      (id := binder.id) (type := payload)
      (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) nextState transition
    exact ⟨resultContext, outcome, after, finalMap, finalWorld,
      TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letUninitialized (lookupStatement?_sound found) form mono extended .append) trace,
      represented, finalHeaps,
      (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
      (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
      preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata, lexical.bind extended, ⟨finalState, protocol.trans allocationRelated tailRelated⟩⟩
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType initial allocation annotation same remaining ih =>
    rw [sequence_rename] at evaluated
    obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := evaluated.bind_computation
    obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented, middleHeaps, maps, worlds, preservation, metadata, transition⟩ :=
      expressionReflects initialSize (Nat.le_of_lt (Nat.lt_of_lt_of_le initialSmaller bounded)) _ contextValid initial initialFound
        environments heaps locals agrees actualTyped state initialEval
    cases represented with
    | fault matched =>
      cases initialTrace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LanguageResult.bind_failure _ initialEval.sound)
        exact ⟨context, _, middle, middleMap, middleWorld, TypedScopedStatements.head_fault mode rest (.letInitializer (lookupStatement?_sound found) form mono failed.sound),
          .fault matched, middleHeaps, maps, worlds, preservation, metadata, ⟨_, _, _, .here, environments.extend maps worlds, locals.mono metadata⟩, transition⟩
    | value payload =>
      cases initialTrace with | value initialTrace =>
        obtain ⟨middleState, expressionRelated⟩ := transition
        have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, allocationTransition⟩ :=
          TypedLexicalControl.Stateful.allocate_initialized functions definitions registered protocol producer mono extended ordinary allocation annotation same (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds) reference frameRead .append middleState ((acquire _ _ conditioned) middleState frameRead)
        obtain ⟨nextState, allocationRelated⟩ := allocationTransition
        obtain ⟨branchSize, branchSmaller, branchEval⟩ := evaluated.bind_success initialEval.sound
        obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, lexical, tailTransition⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_trans smaller branchSmaller) bounded)) (extend contextValid extended)
            nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1
              nextState conditioned tailEval
        obtain ⟨finalState, tailRelated⟩ := stateBindings.restore_reached
          (reached := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
          (id := binder.id) (type := lowered.type)
          (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) nextState tailTransition
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          TypedScopedStatements.prepend (lookupStatement?_sound found) (by intro _ _ expression; simp [form]) (.letInitialized (lookupStatement?_sound found) form initialTrace.sound mono extended .append) trace,
          related, finalHeaps,
          maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
          worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
          preservation.trans (allocationFrame.trans finalFrame), metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata), lexical.bind extended,
          ⟨finalState, protocol.trans expressionRelated (protocol.trans allocationRelated tailRelated)⟩⟩
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
    rw [LoopRenaming.discard] at evaluated
    obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := evaluated.bind_computation
    obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, trace, represented, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, transition⟩ :=
      expressionReflects childSize (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller bounded)) _ contextValid child expressionFound
        environments heaps locals agrees actualTyped state childEvaluation
    cases represented with
    | fault matched =>
      cases trace with | fault failed =>
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic evaluated.sound (LocalSequence.discard_failure _ childEvaluation.sound)
        exact ⟨context, _, middle, middleMap, middleWorld,
          head_fault mode rest (.expression (lookupStatement?_sound found) form failed.sound),
          .fault matched, middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata,
          ⟨_, _, _, .here, environments.extend firstMaps firstWorlds, locals.mono firstMetadata⟩, transition⟩
    | @value _ coreValue payload =>
      cases trace with | value childTrace =>
        obtain ⟨middleState, expressionRelated⟩ := transition
        obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := evaluated.bind_success childEvaluation.sound
        obtain ⟨resultContext, outcome, after, finalMap, finalWorld, tail, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
          ih tailSize (Nat.le_of_lt (Nat.lt_of_lt_of_le tailSmaller bounded)) contextValid
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (GenericExpressionMeaning.agree_prefix agrees coreValue)
            (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
            ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            middleState conditioned
            (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
        obtain ⟨finalState, tailRelated⟩ := transition
        exact ⟨resultContext, outcome, after, finalMap, finalWorld,
          prepend (lookupStatement?_sound found) (not_tail form guard)
            (.expression (lookupStatement?_sound found) form childTrace.sound) tail,
          related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
          firstFrame.trans preservation, firstMetadata.trans metadata, lexical, ⟨finalState, protocol.trans expressionRelated tailRelated⟩⟩
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerIH remainingIH =>
    have innerBound : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) false statements expected type innerCode := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        innerIH child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    have tailBound : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) mode rest expected type body := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        remainingIH child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.sequence_reflects_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.block_reflects_at_for (validity := validity)
          (protocol := protocol) (condition := condition)
          (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
          (globals := globals) budget child within found form innerBound) tailBound
        contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
    have branchBound {statements : List StatementId} {branch : Expr}
        (meaning : ∀ child, child ≤ budget → ∀ (valid : validity context)
          {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
          {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
          {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value},
          DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions →
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
          Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
          RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
          canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) →
          store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) → contextLocation ∉ mapping →
          ∀ state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
          condition contextLocation native → EvaluationSize child actual store (branch.rename ξ) value finalStore →
          ∃ finalContext outcome after finalMap finalWorld,
            Executes false program context evidence source environment before statements finalContext outcome after ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ AdministrativePreserved mapping store finalMap finalStore ∧
            Dynamic.HeapMetadataExtend before after ∧ LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment finalContext after ∧
            Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
        ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
          functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
          child (scope := scope) false statements expected type branch := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        meaning child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    have tailBound : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) mode rest expected type body := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        remainingIH child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.sequence_reflects_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.conditional_reflects_at_for (validity := validity)
          (protocol := protocol) (condition := condition)
          (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) budget child within expressionReflects found form conditionFound conditionType conditionTree
          (branchBound thenIH) (branchBound elseIH)) tailBound
        contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩

  | @terminalBlock context scope mode id node statements rest expected type innerCode body exactUnique found form inner stops issued innerIH =>
    have innerBound : ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
        functions program evidence (source := source) (context := context)
        (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
        child (scope := scope) false statements expected type innerCode := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        innerIH child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.sequence_stopped_reflects_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.block_reflects_at_for (validity := validity)
          (protocol := protocol) (condition := condition)
          (functions := functions) (program := program) (evidence := evidence) (frameLayout := frame)
          (globals := globals) budget child within found form innerBound)
        (GenericLexicalStatements.block_terminates exactUnique found form stops)
        contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩

  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
    have branchBound {statements : List StatementId} {branch : Expr}
        (meaning : ∀ child, child ≤ budget → ∀ (valid : validity context)
          {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
          {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
          {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value},
          DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog) mapping world administrative scope environment canonical ambient.definitions →
          CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
          Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
          RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
          canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) →
          store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) → contextLocation ∉ mapping →
          ∀ state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
          condition contextLocation native → EvaluationSize child actual store (branch.rename ξ) value finalStore →
          ∃ finalContext outcome after finalMap finalWorld,
            Executes false program context evidence source environment before statements finalContext outcome after ∧
            FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
            CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
            LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧ AdministrativePreserved mapping store finalMap finalStore ∧
            Dynamic.HeapMetadataExtend before after ∧ LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
              context scope environment finalContext after ∧
            Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
        ∀ child, child ≤ budget → RecursiveNamedLexicalContracts.Stateful.ReflectsAtFor protocol condition (validity := validity)
          functions program evidence (source := source) (context := context)
          (registry := registry) (faults := faults) (frameLayout := frame) (globals := globals)
          child (scope := scope) false statements expected type branch := by
      intro child within valid mapping world administrative actualContext environment canonical actual before store finalStore ξ contextLocation native value
        environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
        meaning child within valid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
      obtain ⟨sourceSize, sized⟩ := ExecutesAt.has_size trace
      exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, sized, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩
    obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩ :=
      RecursiveNamedLexicalControlBounds.Stateful.sequence_stopped_reflects_at_for (validity := validity)
        (protocol := protocol) (condition := condition)
        (functions := functions) (program := program) (evidence := evidence)
        (frameLayout := frame) (globals := globals) budget size bounded found (by intro expression; simp [form])
        (fun child within => RecursiveNamedLexicalControlBounds.Stateful.conditional_reflects_at_for (validity := validity)
          (protocol := protocol) (condition := condition)
          (functions := functions) (program := program) (evidence := evidence)
          (frameLayout := frame) (globals := globals) budget child within expressionReflects found form conditionFound conditionType conditionTree
          (branchBound thenIH) (branchBound elseIH))
        (GenericLexicalStatements.conditional_terminates exactUnique found form thenStops elseStops)
        contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated
    exact ⟨resultContext, outcome, after, finalMap, finalWorld, trace.sound,
      related, finalHeaps, maps, worlds, preservation, metadata, lexical, transition⟩

include definitions registered producer stateBindings acquire in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedStateTransition.PreservesAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (state : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_at_for functions definitions registered program evidence protocol condition producer stateBindings acquire
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionPreserves tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped state conditioned trace

include definitions registered producer stateBindings acquire in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      ProtectedStateTransition.ReflectsAt protocol (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults child) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
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
    (conditioned : condition contextLocation native)
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after ∧
      Transition protocol state ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_at_for functions definitions registered program evidence protocol condition producer stateBindings acquire
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionReflects tree contextValid environments heaps locals agrees actualTyped reference read unmapped state conditioned evaluated

end Stateful

open ProtectedStateTransition

private def legacyBindings (bindings : ProtectedExpressionMeaning.Binds entry) :
    Bindings (ProtectedStateTransition.Lexical.legacyProtocol entry) where
  prepend state _id _type _value := ⟨bindings.prepend state.down⟩
  prepend_related _state _id _type _value := trivial
  prepend_records _state _id _type _value := rfl
  restore state := ⟨bindings.restore state.down⟩
  restore_related _state := trivial
  restore_records _state := rfl

private def legacyProducer (functions : FunctionModel values.checked.catalog ambient)
    (transport : ProtectedExpressionMeaning.Transport entry) (bindings : ProtectedExpressionMeaning.Binds entry) :
    OrdinaryAllocation.Producer (ProtectedStateTransition.Lexical.legacyProtocol entry) layouts frame
      (CompatibleAmbientHeap.payloadModel values.checked registry functions) :=
  OrdinaryAllocation.of_administrative _ (ProtectedStateTransition.Lexical.legacyTransport transport)
    (legacyBindings bindings) layouts frame (CompatibleAmbientHeap.payloadModel values.checked registry functions)

include definitions registered transport bindings in
theorem preserves_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preservation, metadata, lexical, _⟩ :=
    Stateful.preserves_at_for functions definitions registered program evidence
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      (legacyProducer functions transport bindings) (legacyBindings bindings)
      (fun location native _ => OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      validity extend budget size bounded
      (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.legacy_expression_preserves
        functions program evidence transport (expressionPreserves child within context valid))
      tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, preservation, metadata, lexical⟩

include definitions registered transport bindings in
theorem preserves_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionPreserves : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.PreservesAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    (unique : NodeOccurrencesUnique source)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
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
    (trace : ExecutesAt size mode program context evidence source environment before statements resultContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact preserves_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionPreserves tree contextValid unique environments heaps locals agrees actualTyped reference read unmapped installed trace

include definitions registered transport bindings in
theorem reflects_at_for (validity : SourceSemantics.Context → Prop)
    (extend : ∀ {context nextContext binder}, validity context → BinderExtends source.owner context binder nextContext → validity nextContext) (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, validity context →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : validity context)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
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
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  obtain ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, preservation, metadata, lexical, _⟩ :=
    Stateful.reflects_at_for functions definitions registered program evidence
      (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      (legacyProducer functions transport bindings) (legacyBindings bindings)
      (fun location native _ => OrdinaryAllocation.administrative_readyAt _ _ _ _ _ _ location native)
      validity extend budget size bounded
      (fun child within context valid => RecursiveNamedLexicalContracts.Stateful.legacy_expression_reflects
        functions program evidence transport (expressionReflects child within context valid))
      tree contextValid environments heaps locals agrees actualTyped reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, resultContext, outcome, after, finalMap, finalWorld, trace, represented,
    finalHeaps, maps, worlds, preservation, metadata, lexical⟩

include definitions registered transport bindings in
theorem reflects_at (budget size : Nat) (bounded : size ≤ budget)
    (expressionReflects : ∀ child, child ≤ budget → ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
      RecursiveNamedBoundedContracts.ReflectsAt child (CompatibleAmbientHeap.payloadModel values.checked registry functions)
        program context evidence source (expressions context) faults entry) {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError values source expressions
      context scope mode statements expected type code)
    (contextValid : CompatibleExpressionLiterals.ContextValid solved context evidence)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
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
    (evaluated : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize resultContext outcome after finalMap finalWorld,
      ExecutesAt sourceSize mode program context evidence source environment before statements resultContext outcome after ∧
      FlowRep (registry := registry) functions finalMap finalWorld faults expected type outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      LexicalResult values.checked ambient.definitions finalMap finalWorld administrative source.owner
        context scope environment resultContext after := by
  exact reflects_at_for functions definitions registered program evidence transport bindings
    (fun context => CompatibleExpressionLiterals.ContextValid solved context evidence) (fun valid extended => valid_extend valid extended)
    budget size bounded expressionReflects tree contextValid environments heaps locals agrees actualTyped reference read unmapped installed evaluated

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedLexicalTreeBounds
