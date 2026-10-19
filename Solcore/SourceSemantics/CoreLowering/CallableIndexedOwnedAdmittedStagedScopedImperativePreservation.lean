import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedBitNotSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareBitNotSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerBitNotInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
import Solcore.SourceSemantics.Staging.RecursiveControlViews
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedMatchTreeHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBlockSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion

/-! Scoped compiler statements include control flow, projected writes and unary
updates. Strict child bounds follow the original Source relation, and writes
use the heap reached by their actual key and operand evaluations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape PositionShape)
open CallableIndexedOwnedAdmittedStagedImperativePositions (PositionTyping InitializerTyping)
open GenericImperativeMatch (Tree)
open TypedLexicalControl (sequence_rename)
universe u

open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (bindings : ProtectedStateTransition.Bindings callerProtocol)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
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

include bridge bindings definitions registered producer acquire transport extension faithful observations in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
theorem preserves_position {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions callerProtocol invocation.source invalidProjection missingDefault receiving
      (fun reason token => faults (.semantic reason) token))
    (shape : PositionShape invocation.source position)
    (sourceTyped : PositionTyping invocation.source context position)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    CallableIndexedOwnedAdmittedStagedImperativePositions.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope position expected type code budget := by
  revert shape sourceTyped projection
  induction catalogSites with
  | @body context scope mode statements expected type code syntaxTree body =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      exact CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation.preserves bridge bindings functions definitions registered producer.toOrdinary condition acquire children unique
        body shape projection within environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted trace
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      have tailShape := shape.tail_of_let found form
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent unique found form extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form mono extended trace with
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
              ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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
            exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion.child_and_tail unique
          (lookupStatement?_sound found) form continuing trace with
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
              ih tailShape (ProtectedStateImperativeStatementSuffixTyping.discard unique sourceTyped found form) projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨_, tailShape⟩ := shape.assignment_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      ·
        obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
          (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          functions extension head bare environments heaps locals agrees
        rcases CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion.child_and_tail unique found form snapshot trace with
          ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
          ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, contextEq, outcomeEq, childTrace,
            currentRead, rootType, initialized, path, invalid⟩ |
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
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        · subst finalContext
          subst outcome
          have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_operands
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type)
              (PreparedAssignmentReachedDiagnostics.operands headErrors semantic)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge
              (context := context) (expected := expected) (failure := .semantic (.invalidAssignmentOperands operator)) reached stable⟩
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
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form)
              projection tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
      ·
        have splitTrace := CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion.child_and_tail
          unique found form bare trace
        cases splitTrace with
        | rootFault failed => exact False.elim (failed.excluded head.writable locals)
        | keysFault ready keyTrace =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_key_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        | getterFault keyTrace failed =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_getter_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial)
                keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | rhsFault keyTrace snapshot childTrace =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        | writeFault keyTrace snapshot childTrace failed =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_write_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial)
                keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | success keyTrace snapshot childTrace write remainingTrace =>
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
                count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form)
                projection (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
  | @bitNotProjected context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨_word, tailShape⟩ := shape.unary_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with | intro typed _ => exact typed
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have splitTrace := CallableIndexedOwnedPreparedStagedScopedProjectedBitNotSourceInversion.child_and_tail
        unique found form head.projected trace
      cases splitTrace with
      | rootFault failed => exact False.elim (failed.excluded head.writable locals)
      | keysFault ready keyTrace =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_key_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
      | getterFault keyTrace failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_getter_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren (PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment) headErrors assignmentDiagnostics targetTyped initial)
              keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
      | success keyTrace snapshot write remainingTrace =>
          obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
              count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_value
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot write
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.bitNot unique sourceTyped found form)
              projection (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨innerShape, restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
      have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (innerIH innerShape innerTyped projection)
        unique found form (.inl (remainingIH restShape restTyped projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenIH elseIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.preserves bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        unique found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix unique sourceTyped found form) projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (ih innerShape innerTyped projection)
        unique found form (.inr stops) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.preserves bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        unique found form (.inr ⟨thenStops, elseStops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @whileLoop context scope mode id node conditionId conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopBodyErrors remainingErrors loopIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨loopShape, restShape⟩ := shape.loop found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children unique sourceTyped found form).2
      have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedWhileSequences.preserves bridge functions condition transport
        (children _) conditionFound conditionType typed certified nativeTyped
        (loopIH loopShape loopTyped projection)
        unique found form (remainingIH restShape restTyped projection) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren remaining catalog patternContext childErrors remainingErrors matchIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            PreservesAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire unique childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.preserves bridge functions condition
          selectedMeaning unique found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix unique sourceTyped found form) projection)) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren stops issued catalog patternContext childErrors matchIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            PreservesAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire unique childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.preserves bridge functions condition
          selectedMeaning unique found form (.inr stops) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @breaking context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.breaking_view unique found form trace
      exact ⟨_, store, mapping, world, LocalLoop.breaking_evaluates _ actual store,
        .breaking environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @continuing context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨rfl, rfl, rfl⟩ := Staging.Recursive.Size.StatementsIn.continuing_view unique found form trace
      exact ⟨_, store, mapping, world, LocalLoop.continuing_evaluates _ actual store,
        .continuing environment, heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted finalContext outcome after trace
      obtain ⟨_word, _bare, tailShape⟩ := shape.bitNot_tail found form head.bare
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      rcases CallableIndexedOwnedPreparedStagedScopedBareBitNotSourceInversion.child_and_tail unique found form head.bare trace with
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
          maps, worlds, preservation, .refl _, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic reason) reached stable⟩
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
          ih tailShape (ProtectedStateImperativeStatementSuffixTyping.bitNot unique sourceTyped found form)
            projection tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
  | @forLoop context scope mode id node items test post statements rest expected type initialCode body found form initialTree remaining initialErrors remainingErrors initialIH remainingIH =>
      intro shape sourceTyped projection size
      obtain ⟨initialShape, postShape, loopShape, restShape⟩ := shape.for_children found form
      have initialTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.children unique sourceTyped found form
      have tailTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedForSequences.preserves (size := size) bridge functions condition
        (initialIH ⟨initialShape, postShape, loopShape⟩ initialTyped projection) unique found form
        (remainingIH restShape tailTyped projection)
  | @initializersDone context scope test node post statements expected type testCode bodyCode postCode selfReason found nodeType certified bodyTree postTree nativeTyped bodyErrors postErrors bodyIH =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      obtain ⟨control, _testTyped, bodyTyped, postTyped⟩ := InitializerTyping.nil sourceTyped
      obtain ⟨typedNode, typedFound, typed, generated⟩ := certified
      cases Option.some.inj (found.symm.trans typedFound)
      have postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope post expected type postCode budget :=
        CallableIndexedOwnedAdmittedStagedForHeaderPreservation.preserves_at bridge bindings transport functions faithful observations extension
          definitions registered producer condition acquire assignmentDiagnostics children unique postTree postErrors semantic shape.2.1 postTyped
      obtain ⟨loopSize, rawOutcome, sameSize, outcomeEq, loopTrace⟩ :=
        CallableIndexedOwnedAdmittedStagedForInitializerSource.nil trace
      rw [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore loopTrace] at outcomeEq
      subst outcome
      have loopWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      exact CallableIndexedOwnedAdmittedStagedForHeads.preserves bridge functions condition transport
        (children _) found nodeType typed generated nativeTyped (bodyIH shape.2.2 bodyTyped projection) postCorrect
        loopWithin environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted loopTrace
  | @initializerUninitialized context nextContext scope binder rest body payload test post statements expected type mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      have tailShape := shape.1.let_tail
      obtain ⟨tailSize, location, bound, nextOutcome, sameSize, outcomeEq, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedAdmittedStagedForInitializerSource.absent extended trace
      subst outcome
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih ⟨tailShape, shape.2⟩ (InitializerTyping.absent sourceTyped extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
          nextReference nextRead (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted remainingTrace
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨value, finalStore, finalMap, finalWorld, .letE allocationEval evaluated, (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions represented), finalHeaps,
        (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation allocated).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated
          (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest test post statements expected type mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      have tailShape := shape.1.let_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.initialized mono extended trace with
        ⟨initialSize, failure, sameSize, outcomeEq, initialTrace⟩ |
        ⟨initialSize, tailSize, sourceValue, location, middle, bound, nextOutcome, sameSize, outcomeEq, initialTrace, allocated, remainingTrace⟩
      · subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
        obtain ⟨value, finalStore, finalMap, finalWorld, initialEval, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context initialSize initialStrict certified initialFound typed environments heaps locals agrees actualTyped
            initial admitted initialTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LanguageResult.bind_failure _ initialEval,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · subst outcome
        have initialStrict : initialSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
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
              ih ⟨tailShape, shape.2⟩ (InitializerTyping.initialized sourceTyped mono extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
                nextReference nextRead (allocationFrame contextLocation
                  (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                  (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted remainingTrace
            let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (id := binder.id) (type := lowered.type)
              (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
            refine ⟨value, finalStore, finalMap, finalWorld,
              LanguageResult.bind_success _ initialEval (.letE allocationEval evaluated), (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions related), finalHeaps,
              maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
              worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
              preservation.trans (allocationFrame.trans finalFrame),
              metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation allocated).trans finalMetadata),
              finalState, callerProtocol.trans expressionRelated (callerProtocol.trans allocationRelated
                (callerProtocol.trans tailRelated (bindings.restore_related
                  (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
                  (id := binder.id) (type := lowered.type)
                  (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
            exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
              (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @initializerDiscard context scope expression expressionNode rest lowered body test post statements expected type expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      have tailShape := shape.1.discard_tail
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have same := Option.some.inj (expressionFound.symm.trans typedFound)
      cases same
      rw [LoopRenaming.discard]
      rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.expression trace with
        ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
        ⟨childSize, tailSize, sourceValue, middle, sameSize, childTrace, remainingTrace⟩
      · subst outcome
        have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
        obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, post⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | fault matched => exact ⟨_, finalStore, finalMap, finalWorld, LocalSequence.discard_failure _ evaluated,
            .fault matched, finalHeaps, maps, worlds, preservation, metadata, reached, related, post.at_fault_type⟩
      · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
        have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
          rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
        obtain ⟨value, middleStore, middleMap, middleWorld, first, represented,
            middleHeaps, firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost⟩ :=
          children context childSize childStrict certified expressionFound typed environments heaps locals agrees actualTyped
            initial admitted childTrace
        cases represented with
        | @value sourceValue coreValue payload =>
            obtain ⟨value, finalStore, finalMap, finalWorld, second, related,
                finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
              ih ⟨tailShape, shape.2⟩ (InitializerTyping.expression sourceTyped) projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @initializerAssign context scope assignment operator rhs rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      obtain ⟨_, tailShape⟩ := shape.1.assignment_tail
      have assignmentTyped := (InitializerTyping.assignment sourceTyped).1
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      ·
        obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
          (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          functions extension head bare environments heaps locals agrees
        rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment snapshot trace with
          ⟨childSize, failure, sameSize, outcomeEq, childTrace⟩ |
          ⟨childSize, right, currentCell, initialValue, currentSelected, sameSize, outcomeEq, childTrace,
            currentRead, rootType, initialized, path, invalid⟩ |
          ⟨childSize, tailSize, right, middle, written, updated, sameSize, childTrace, write, remainingTrace⟩
        · subst outcome
          have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) childTrace body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        · subst outcome
          have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_operands
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              (typedChildren childSize childStrict) snapshot invalid childTrace body (LocalLoop.controlType type)
              (PreparedAssignmentReachedDiagnostics.operands headErrors semantic)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge
              (context := context) (expected := expected) (failure := .semantic (.invalidAssignmentOperands operator)) reached stable⟩
        · have childStrict : childSize < budget := Nat.lt_of_lt_of_le (by
            rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega) within
          have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
            rw [sameSize]; simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]; omega)) within
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
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.assignment sourceTyped).2 projection tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
      ·
        have splitTrace := CallableIndexedOwnedAdmittedStagedForInitializerProjectedInversion.projected_assignment bare trace
        cases splitTrace with
        | rootFault failed => exact False.elim (failed.excluded head.writable locals)
        | keysFault ready keyTrace =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_key_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        | getterFault keyTrace failed =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_getter_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial)
                keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | rhsFault keyTrace snapshot childTrace =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
        | writeFault keyTrace snapshot childTrace failed =>
            obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
                preservation, metadata, reached, related, stable⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_write_fault
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren (PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic assignmentDiagnostics assignmentTyped initial)
                keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
            exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | success keyTrace snapshot childTrace write remainingTrace =>
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
                count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
                (compiled := compiled) (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
                (context := context) (scope := scope) (administrative := administrative)
                bridge functions extension transport faithful observations
                head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot childTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) write
            obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih ⟨tailShape, shape.2⟩ (InitializerTyping.assignment sourceTyped).2
                projection (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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
  | @initializerBitNot context scope assignment rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      obtain ⟨_word, _bare, tailShape⟩ := shape.1.bitNot_tail head.bare
      have assignmentTyped := (InitializerTyping.bitNot sourceTyped).1
      rcases CallableIndexedOwnedAdmittedStagedForInitializerSource.bitNot head.bare trace with
        ⟨reason, sameSize, outcomeEq, heapEq, failed⟩ |
        ⟨tailSize, target, updated, written, sameSize, snapshot, write, remainingTrace⟩
      ·
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
          maps, worlds, preservation, .refl _, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic reason) reached stable⟩
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
          ih ⟨tailShape, shape.2⟩ (InitializerTyping.bitNot sourceTyped).2 projection tailWithin (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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

  | @initializerBitNotProjected context scope assignment rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted outcome after trace
      obtain ⟨_word, tailShape⟩ := shape.1.unary_tail
      have assignmentTyped := (InitializerTyping.bitNot sourceTyped).1
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with | intro typed _ => exact typed
      have typedChildren (size : Nat) (smaller : size < budget) : PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
        intro scope id lowered generated node found typed
        obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have splitTrace := CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotInversion.projected_bitNot head.projected trace
      cases splitTrace with
      | rootFault failed => exact False.elim (failed.excluded head.writable locals)
      | keysFault ready keyTrace =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_key_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren ready keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge reached stable⟩
      | getterFault keyTrace failed =>
          obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds,
              preservation, metadata, reached, related, stable⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_getter_fault
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren (PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment) headErrors assignmentDiagnostics targetTyped initial)
              keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) failed body (LocalLoop.controlType type)
          exact ⟨_, finalStore, finalMap, finalWorld, evaluated, .fault matched, finalHeaps, maps, worlds,
            preservation, metadata, reached, related, CallableIndexedOwnedAdmittedStagedImperativeFlow.fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
      | success keyTrace snapshot write remainingTrace =>
          obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, preservation, metadata,
              count, typed, ⟨reached, related, nextAdmitted⟩, continuation⟩ :=
            CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_value
              (compiled := compiled) (values := .initial compiled.compatible.checked)
              (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
              (context := context) (scope := scope) (administrative := administrative)
              bridge functions extension transport faithful observations
              head head.projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
              budget typedChildren keyTrace (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) snapshot write
          obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.bitNot sourceTyped).2
              projection (by simp only [Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero] at within; omega) (environments.extend maps worlds) middleHeaps (locals.mono metadata)
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

include bridge bindings definitions registered producer acquire transport extension faithful observations in
theorem preserves_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      PreservesAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
    {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.CatalogSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (assignmentDiagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked)
      functions callerProtocol invocation.source invalidProjection missingDefault receiving
      (fun reason token => faults (.semantic reason) token))
    {mode : Bool} {statements : List StatementId}
    (atStatements : position = .statements mode statements)
    (shape : Shape invocation.source mode statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
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
    {finalContext : SourceSemantics.Context} {outcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.StatementsIn program stages mode size invocation context environment before
      statements finalContext outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases atStatements
  exact preserves_position bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
    children unique tree catalogSites semantic assignmentDiagnostics shape sourceTyped projection within
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
