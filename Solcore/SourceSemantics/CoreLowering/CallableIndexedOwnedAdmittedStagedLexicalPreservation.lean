import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion

/-! Straight-line lexical statements retain their actual Source contexts and
marked native allocations. Child bounds are strict numeric hypotheses; the
compiler tree contains only typing, syntax and accepted allocator receipts. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (Shape TypedCertificate)
open GenericLexicalStatements (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedLexicalFlow (result Represents restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

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
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates) context scope mode statements expected type code)
    (tailMode : mode = true) (shape : Shape invocation.source statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
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
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements program stages size invocation context environment before
      statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context expected (result outcome) reached := by
  induction tree generalizing size mapping world administrative actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @nil context scope mode expected type allowed =>
      cases tailMode
      have rawUnit : expected = .unit := allowed.resolve_left (by decide)
      subst expected
      have coreUnit : type = .unit := (Except.ok.inj projection).symm
      subst type
      cases trace
      refine ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates .unit actual store,
        .fallthrough environment rfl rfl, heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, ?_⟩
      exact ⟨admitted.rows, by intro source same; cases same; exact ⟨.unit, admitted.heap⟩⟩
  | @returnUnit context scope mode id node rest found form =>
      obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedLexicalSourceInversion.return_unit unique found form trace
      refine ⟨_, store, mapping, world, LocalLoop.returned_evaluates (.unit : Evaluates actual store .unit .unit store),
        .returned .unit, heaps, .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, ?_⟩
      exact ⟨admitted.rows, by intro source same; cases same; exact ⟨.unit, admitted.heap⟩⟩
  | @returnValue context scope mode id node expression expressionNode expected lowered rest found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression (id :: rest) :=
        .returning rest (lookupStatement?_sound found) form
      obtain ⟨childSize, childOutcome, sameSize, contextEq, outcomeEq, childTrace⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique head trace
      subst finalContext
      subst outcome
      obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) childTrace
          (by simpa only [sameSize] using within)
      cases valueType
      cases represented with
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @tail context scope id node expression expressionNode expected lowered found form expressionFound valueType child =>
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      have head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression [id] :=
        .tail (lookupStatement?_sound found) form
      obtain ⟨childSize, childOutcome, sameSize, contextEq, outcomeEq, childTrace⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body unique head trace
      subst finalContext
      subst outcome
      obtain ⟨_sourceTrace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
          maps, worlds, preservation, metadata, reached, related, post⟩ :=
        CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge head certified expressionFound typed
          environments heaps locals agrees actualTyped initial admitted budget (children context) childTrace
          (by simpa only [sameSize] using within)
      cases valueType
      cases represented with
      | returned payload => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .returned payload, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
      | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, evaluated,
          .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalSourceInversion.absent unique found form extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailMode tailShape projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, represented, finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedLexicalSourceInversion.initialized unique found form extended trace with
        ⟨initialSize, failure, sameSize, contextEq, outcomeEq, initialTrace⟩ |
        ⟨initialSize, tailSize, sourceValue, location, middle, bound, sameSize, initialTrace, allocated, remainingTrace⟩
      · subst finalContext
        subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, initialEval, represented,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
            obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
                nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
              CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
                mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
                reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) initialPost.at_value.2
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
              ih tailMode tailShape projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), related, finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact restore_post bridge bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
      cases tailMode
      obtain ⟨rfl, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail unique
          (lookupStatement?_sound found) form trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
            middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
                finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
              ih rfl tailShape projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | block found form inner remaining innerIH remainingIH => exact False.elim (shape.not_block found form)
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
      exact False.elim (shape.not_if found form)
  | terminalBlock _ found form inner stops issued ih => exact False.elim (shape.not_block found form)
  | terminalIf _ found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
      exact False.elim (shape.not_if found form)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedLexicalPreservation
