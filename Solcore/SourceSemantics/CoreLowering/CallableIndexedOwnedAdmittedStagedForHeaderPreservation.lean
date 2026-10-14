import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderPost

/-! Actual staged post-header execution determines the emitted native result.
The outer caller is restored while allocations and capture writes are retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (ItemShape)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open GenericForHeader (Tree)
open TypedLexicalControl (sequence_rename)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)

  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

theorem fault_post {context : SourceSemantics.Context} {index : ProtectedStateTransition.Index}
    {expected : TypeSystem.Ty} {failure : Staging.Recursive.Failure}
    (reached : callerProtocol.State index)
    (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows (bridge.pool reached)) :
    PostAdmission bridge context expected (.fault failure) reached := by
  cases failure with
  | semantic reason => exact ⟨stable, by intro value same; cases same⟩
  | stage origin call reason => exact stable

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  (definitions : layouts.definitions = (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (registered : frame.Registered (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (producer : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions))
  (condition : Location → NativeFrame → Prop)
  (acquire : ∀ location native, condition location native →
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

private theorem rep_environment {mapping world expected type outcome value first second}
    (related : Represents model mapping world false expected type faults (restoredOutcome first outcome) value) :
    Represents model mapping world false expected type faults (restoredOutcome second outcome) value := by
  cases outcome with
  | done environment => cases related with | fallthrough _ allowed => exact .fallthrough _ allowed
  | fault failure => exact related

private theorem post_environment {context expected outcome first second index}
    {reached : callerProtocol.State index}
    (post : Post bridge context expected (restoredOutcome first outcome) reached) :
    Post bridge context expected (restoredOutcome second outcome) reached := by
  cases outcome <;> exact post

include bridge bindings definitions registered producer acquire transport extension in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy}
    {catalogRegistry : SourceCoreRawMetadata.Registry} {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : tree.ErrorsFor diagnosticPolicy catalogRegistry catalogFaults)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
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
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.ForItemsOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.ForItems program stages size invocation context environment before
      items finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached := by
  induction catalogSites generalizing size mapping world actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @nil context scope code next =>
      obtain ⟨rfl, rfl, rfl⟩ := CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.empty trace
      change code = LocalLoop.fallthrough type at next
      subst code
      rw [LoopRenaming.fallthrough]
      exact ⟨_, store, mapping, world, LocalLoop.fallthrough_evaluates type actual store,
        .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended) tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, (rep_environment functions represented), finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initialFound sourceType child allocation annotation same remaining tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized extended trace with
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
              CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
                mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
                reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) initialPost.at_value.2
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, related,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
              ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended) tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), (rep_environment functions related), finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @discard context scope expression expressionNode rest lowered body expressionFound child remaining tailSites ih =>
      have tailShape := shape.discard_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression trace with
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
              ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped) tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope assignment operator rhs rest body head remaining tailSites headErrors ih =>
      have invalidToken : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid := by
        intro previous right invalid
        exact semantic _ _ ((GenericAssignmentStatements.Head.ErrorsFor.reachable headErrors).operands previous right invalid)
      obtain ⟨_profile, bare, tailShape⟩ := shape.assign_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
        (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        functions extension head bare environments heaps locals agrees
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
        ⟨childSize, right, currentCell, initialValue, selected, sameSize, contextEq, outcomeEq,
          childTrace, _currentRead, _rootType, _initialized, _path, invalidOperands⟩ |
        ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (typedChildren childSize childStrict) childTrace body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
          preservation, metadata, reached, related, fault_post bridge reached stable⟩
      · subst finalContext
        subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_operands
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (typedChildren childSize childStrict) snapshot invalidOperands childTrace body (LocalLoop.controlType type) invalidToken
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
          preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected)
            (failure := .semantic (.invalidAssignmentOperands operator)) reached stable⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp)) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
            count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (typedChildren childSize childStrict) snapshot childTrace write
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2 tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted remainingTrace
        have native := (continuation body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using evaluated)
        exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
          maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
          last, callerProtocol.trans related lastRelated, post⟩
  | @bitNot context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_word, _bare, tailShape⟩ := shape.bitNot_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.bitNot trace with
        ⟨reason, sameSize, contextEq, outcomeEq, heapEq, failed⟩ |
        ⟨tailSize, target, updated, written, sameSize, snapshot, write, remainingTrace⟩
      ·
        subst finalContext
        subst outcome
        subst after
        obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
            preservation, reached, related, stable⟩ :=
          CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_fault
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions transport head environments heaps locals agrees initial admitted
            headErrors failed body (LocalLoop.controlType type)
        exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault (semantic _ _ matched), finalHeaps,
          maps, worlds, preservation, .refl _, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic reason) reached stable⟩
      · have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
            count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_value
            (compiled := compiled) (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
            (context := context) (scope := scope) (administrative := administrative)
            bridge functions transport head environments heaps locals agrees actualTyped initial admitted assignmentTyped
            snapshot write
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2 tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees slots) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted remainingTrace
        have native := (continuation body (LocalLoop.controlType type)).wrap (by
          simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift,
            SourceCoreDataPlaces.shift] using evaluated)
        exact ⟨value, finalStore, finalMap, finalWorld, native, represented, finalHeaps,
          maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame, metadata.trans finalMetadata,
          last, callerProtocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
