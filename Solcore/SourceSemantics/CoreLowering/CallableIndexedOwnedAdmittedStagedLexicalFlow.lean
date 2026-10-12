import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion

/-! Straight-line lexical statements retain their actual Source contexts and
marked native allocations. Child bounds are strict numeric hypotheses; the
compiler tree contains only typing, syntax and accepted allocator receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (Shape TypedCertificate)
open GenericLexicalStatements (Tree)
open TypedLexicalControl (sequence_rename)
universe u

/-- Function-level meaning of the three actual staged body outcomes. -/
def result : Staging.Recursive.BodyOutcome → Staging.Recursive.Outcome
  | .returned value => .value value
  | .fault failure => .fault failure
  | .fallthrough _ => .value .unit

inductive Represents {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (mapping : LocationMap) (world : StoreTyping) (raw : TypeSystem.Ty)
    (type : Ty) (faults : RecursiveStageMeaning.FaultRep) :
    Staging.Recursive.BodyOutcome → Value → Prop where
  | returned {source native} (payload : model.Represents mapping world raw source native type) :
      Represents model mapping world raw type faults (.returned source) (LocalLoop.returnedValue native)
  | fault {failure token} (matched : faults failure token) :
      Represents model mapping world raw type faults (.fault failure)
        (.inLeft (LocalLoop.controlType type) (.word token))
  | fallthrough (environment : Dynamic.Environment) (rawUnit : raw = .unit) (coreUnit : type = .unit) :
      Represents model mapping world raw type faults (.fallthrough environment) (LocalLoop.fallthroughValue type)

theorem Represents.body_result {catalog projects definitions}
    {model : GenericHeap.PayloadModel catalog projects definitions} {mapping world raw type faults outcome value}
    (represented : Represents model mapping world raw type faults outcome value) :
    Staging.Recursive.BodyResult raw outcome (result outcome) := by
  cases represented with
  | returned => exact .returned
  | fault => exact .fault
  | fallthrough environment rawUnit coreUnit => cases rawUnit; exact .unit

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

/-- Restoring the lexical native slot does not discard the allocated Source
heap. Successful Source typing is transported back through the actual binder. -/
theorem restore_post {context nextContext : SourceSemantics.Context}
    {owner : Resolved.DeclarationId} {binder : TypedBinder}
    (extended : BinderExtends owner context binder nextContext)
    {index : ProtectedStateTransition.Index} {type : Ty} {value : Value}
    {raw : TypeSystem.Ty} {outcome : Staging.Recursive.Outcome}
    (reached : callerProtocol.State
      ⟨(binder.id, type) :: index.scope, index.mapping, index.world, index.heap, index.store, value :: index.canonical⟩)
    (post : PostAdmission bridge nextContext raw outcome reached) :
    PostAdmission bridge context raw outcome (bindings.restore reached) := by
  have rows := CallableIndexedOwnedIndirectExpressionHeads.StableRows.after_administrative
    (bridge.pool reached) (bridge.pool (bindings.restore reached)) post.rows (.refl _ _)
  cases outcome with
  | value source =>
      refine ⟨rows, ?_⟩
      intro actual same
      cases same
      obtain ⟨typed, admitted⟩ := post.at_value
      exact ⟨(Dynamic.ValueHasType.iff_of_binderExtends extended).mpr typed,
        (Dynamic.HeapWellTyped.iff_of_binderExtends extended).mpr admitted.heap⟩
  | fault failure =>
      cases failure with
      | semantic reason => exact ⟨rows, by intro source same; cases same⟩
      | stage => exact rows

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.OrdinaryAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

include bridge bindings definitions registered producer acquire in
/-- Native completion determines the actual ordered lexical Source trace,
including the distinct context after successful allocation and initializer
faults before allocation. The returned caller state retains the entire heap. -/
theorem reflects {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope mode statements expected type code)
    (tailMode : mode = true) (shape : Shape invocation.source statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {value : Value}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (conditioned : condition contextLocation native)
    (admitted : Admission bridge context initial)
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize finalContext outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program stages sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context expected (result outcome) reached := by
  induction tree generalizing size mapping world administrative actualContext environment canonical actual before
      store finalStore ξ contextLocation native value with
  | @nil context scope mode expected type allowed =>
      cases tailMode
      have rawUnit : expected = .unit := allowed.resolve_left (by decide)
      subst expected
      have coreUnit : type = .unit := (Except.ok.inj projection).symm
      subst type
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.fallthrough_evaluates .unit actual store)
      refine ⟨_, context, .fallthrough environment, before, mapping, world, .nil,
        .fallthrough environment rfl rfl, heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, ?_⟩
      exact ⟨admitted.rows, by intro source same; cases same; exact ⟨.unit, admitted.heap⟩⟩
  | @returnUnit context scope mode id node rest found form =>
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store))
      refine ⟨_, context, .returned .unit, before, mapping, world,
        .returnUnit (lookupStatement?_sound found) form, .returned .unit, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
      exact ⟨admitted.rows, by intro source same; cases same; exact ⟨.unit, admitted.heap⟩⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression (id :: rest) :=
        .returning rest (lookupStatement?_sound found) form
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) completed within
      cases valueType
      cases represented with
      | returned payload => exact ⟨sourceSize, context, _, after, finalMap, finalWorld, trace,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨sourceSize, context, _, after, finalMap, finalWorld, trace,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression [id] :=
        .tail (lookupStatement?_sound found) form
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) completed within
      cases valueType
      cases represented with
      | returned payload => exact ⟨sourceSize, context, _, after, finalMap, finalWorld, trace,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨sourceSize, context, _, after, finalMap, finalWorld, trace,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailMode tailShape projection (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .letUninitialized (lookupStatement?_sound found) form mono extended .append trace,
        represented, finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename] at completed
      obtain ⟨initialSize, middleStore, input, initialSmaller, initialEval⟩ := completed.bind_computation
      obtain ⟨initialSourceSize, sourceOutcome, middle, middleMap, middleWorld, initialTrace, represented,
          middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
        children context initialSize (Nat.lt_of_lt_of_le initialSmaller within) certified initialFound typed
          environments heaps locals agrees actualTyped initial admitted initialEval
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LanguageResult.bind_failure _ initialEval.sound)
          exact ⟨Staging.Recursive.Size.stepSize [initialSourceSize], context, _, middle, middleMap, middleWorld,
            .letFault (lookupStatement?_sound found) form mono initialTrace, .fault matched,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
              nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih tailMode tailShape projection (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .letInitialized (lookupStatement?_sound found) form initialTrace mono extended .append trace,
            related, finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
      cases tailMode
      obtain ⟨rfl, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard] at completed
      obtain ⟨childSize, middleStore, input, smaller, childEvaluation⟩ := completed.bind_computation
      obtain ⟨sourceSize, childOutcome, middle, middleMap, middleWorld, childTrace, represented,
          middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
        children context childSize (Nat.lt_of_lt_of_le smaller within) certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted childEvaluation
      cases represented with
      | fault matched =>
          obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalSequence.discard_failure _ childEvaluation.sound)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], context, _, middle, middleMap, middleWorld,
            .expressionFault (lookupStatement?_sound found) form childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih rfl tailShape projection (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .discard (lookupStatement?_sound found) form childTrace tailTrace, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | block found form inner remaining innerIH remainingIH => exact False.elim (shape.not_block found form)
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
      exact False.elim (shape.not_if found form)
  | terminalBlock _ found form inner stops issued ih => exact False.elim (shape.not_block found form)
  | terminalIf _ found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
      exact False.elim (shape.not_if found form)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFlow
