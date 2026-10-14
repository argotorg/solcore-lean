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
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion

/-! Scoped compiler statements include conditionals, finite while loops, bare plain assignment,
lexical allocation, discard and return. Strict child bounds run the original recursive
Source relation; writes target the actual heap reached by the RHS. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape PositionShape)
open CallableIndexedOwnedAdmittedStagedImperativePositions (PositionTyping InitializerTyping)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open GenericImperativeMatch (Tree)
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

include bridge bindings definitions registered producer acquire transport extension in
/-- Native completion determines the actual ordered lexical Source trace,
including the distinct context after successful allocation and initializer
faults before allocation. The returned caller state retains the entire heap. -/
theorem reflects_position {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (graph : OccurrenceGraphWellFormed invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {catalogRegistry : SourceCoreRawMetadata.Registry}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : Tree.CatalogSites diagnosticPolicy catalogRegistry catalogFaults tree)
    (shape : PositionShape invocation.source position)
    (sourceTyped : PositionTyping invocation.source context position)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    CallableIndexedOwnedAdmittedStagedImperativePositions.Reflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope position expected type code budget := by
  revert shape sourceTyped projection
  induction catalogSites with
  | @body context scope mode statements expected type code syntaxTree body =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      exact CallableIndexedOwnedAdmittedStagedScopedLexicalFlow.reflects bridge bindings functions definitions registered producer.toOrdinary condition acquire children
        body shape projection within environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted completed
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.tail_of_let found form
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl graph.nodeOccurrencesUnique sourceTyped found form extended) projection (Nat.le_trans (Nat.le_of_lt smaller) within)
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
      exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
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
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl graph.nodeOccurrencesUnique sourceTyped found form extended) projection (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
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
          exact restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
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
            ih tailShape (ProtectedStateImperativeStatementSuffixTyping.discard graph.nodeOccurrencesUnique sourceTyped found form) projection (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          have combined : Staging.Recursive.Size.StatementsIn program stages mode
              (Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize]) invocation context environment before
              (id :: rest) finalContext outcome after := by
            cases semi with
            | true => exact .discard (lookupStatement?_sound found) form childTrace tailTrace
            | false =>
                have falseMode : mode = false := continuing.resolve_left (by decide)
                cases falseMode
                exact .discardValue (lookupStatement?_sound found) form childTrace tailTrace
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
            combined, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, bare, tailShape⟩ := shape.assign_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
        head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
        budget typedChildren completed within
      cases result with
      | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
            .assignBareFault (lookupStatement?_sound found) form snapshot trace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge reached stable
      | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := ProtectedStateImperativeStatementSuffixTyping.assignment graph.nodeOccurrencesUnique sourceTyped found form
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .assignBare (lookupStatement?_sound found) form snapshot childTrace write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨innerShape, restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner graph.nodeOccurrencesUnique sourceTyped found form
      have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.reflects bridge functions condition
        (innerIH innerShape innerTyped projection)
        found form (.inl (remainingIH restShape restTyped projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenIH elseIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.reflects bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form) projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerErrors ih =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.reflects bridge functions condition
        (ih innerShape innerTyped projection)
        found form (.inr ⟨exactUnique, stops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false graph.nodeOccurrencesUnique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
      exact CallableIndexedOwnedAdmittedStagedConditionalSequences.reflects bridge functions condition
        (children _) conditionFound conditionType typed certified
        (thenIH leftShape leftTyped projection) (elseIH rightShape rightTyped projection)
        found form (.inr ⟨exactUnique, thenStops, elseStops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @whileLoop context scope mode id node conditionId conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopBodyErrors remainingErrors loopIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨loopShape, restShape⟩ := shape.loop found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children graph.nodeOccurrencesUnique sourceTyped found form).2
      have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedWhileSequences.reflects bridge functions condition transport
        (children _) conditionFound conditionType typed certified nativeTyped
        (loopIH loopShape loopTyped projection)
        found form (remainingIH restShape restTyped projection) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren remaining catalog patternContext childErrors remainingErrors matchIH remainingIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            ReflectsAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchReflects
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.reflects (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.reflects bridge functions condition
          selectedMeaning found form (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form) projection)) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren stops issued catalog patternContext childErrors matchIH =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      cases compilation with
      | mk values solved sourceCells ambientDefinitions =>
        cases sameValues
        have childMeaning : ∀ childSize, childSize < budget →
            ReflectsAt bridge context model stages invocation
              (TypedCertificate invocation.source certificates context) faults childSize := by
          intro childSize smaller actualScope actualId actualCode certified
          obtain ⟨childNode, childFound, childTyped, actualCertificate⟩ := certified
          exact children context childSize smaller actualCertificate
        have selectedMeaning : CallableIndexedOwnedAdmittedStagedMatchSequences.MatchReflects
            (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
            (stages := stages) (invocation := invocation) (faults := faults)
            bridge functions condition context scope resolution expected type matched budget := by
          intro matchSize
          exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.reflects (size := matchSize)
            bridge functions onError allocator definitions registered extension receipt ordinary
            patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
            budget condition producer bindings acquire childMeaning
            (fun request member childContext selectedContext bodyTyped =>
              matchIH request member childContext selectedContext
                (shape.match_request found form selectedContext.forget) bodyTyped projection)
        obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
        exact CallableIndexedOwnedAdmittedStagedMatchSequences.reflects bridge functions condition
          selectedMeaning found form (.inr ⟨exactUnique, stops⟩) within
          environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
  | @breaking context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.breaking_evaluates _ actual store)
      exact ⟨_, _, .breaking environment, before, mapping, world,
        .breaking (lookupStatement?_sound found) form, .breaking environment, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted⟩
  | @continuing context scope mode id node rest expected type found form =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.continuing_evaluates _ actual store)
      exact ⟨_, _, .continuing environment, before, mapping, world,
        .continuing (lookupStatement?_sound found) form, .continuing environment, heaps,
        .refl _, .refl _, .refl _ _, .refl _, initial, callerProtocol.refl initial, admitted⟩
  | @bitNot _ _ _ _ _ _ _ _ _ _ found form _ _ _ _ _
    =>
      intro shape sourceTyped projection
      intro size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have impossible := shape.head_allowed found
      simp only [form, CallableIndexedOwnedPreparedStagedBranchingTree.allowedForm, Bool.false_eq_true] at impossible
  | @forLoop context scope mode id node items test post statements rest expected type initialCode body found form initialTree remaining initialErrors remainingErrors initialIH remainingIH =>
      intro shape sourceTyped projection
      obtain ⟨initialShape, postShape, loopShape, restShape⟩ := shape.for_children found form
      have initialTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.children graph.nodeOccurrencesUnique sourceTyped found form
      have tailTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix graph.nodeOccurrencesUnique sourceTyped found form
      intro size
      exact CallableIndexedOwnedAdmittedStagedForSequences.reflects (size := size) bridge functions condition
        (initialIH ⟨initialShape, postShape, loopShape⟩ initialTyped projection) found form
        (remainingIH restShape tailTyped projection)
  | @initializersDone context scope test node post statements expected type testCode bodyCode postCode selfReason found nodeType certified bodyTree postTree nativeTyped bodyErrors postErrors bodyIH =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨control, _testTyped, bodyTyped, postTyped⟩ := InitializerTyping.nil sourceTyped
      obtain ⟨typedNode, typedFound, typed, generated⟩ := certified
      cases Option.some.inj (found.symm.trans typedFound)
      have postCorrect : CallableIndexedOwnedAdmittedStagedForPostContracts.Reflects
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope post expected type postCode budget :=
        CallableIndexedOwnedAdmittedStagedForHeaderReflection.reflects_at bridge bindings transport functions extension
          definitions registered producer condition acquire children graph.nodeOccurrencesUnique postTree shape.2.1 postTyped
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
          maps, worlds, preserved, metadata, reached, related, resultPost⟩ :=
        CallableIndexedOwnedAdmittedStagedForHeads.reflects bridge functions condition transport
          (children _) found nodeType typed generated nativeTyped (bodyIH shape.2.2 bodyTyped projection) postCorrect
          within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [], sourceSize], outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps,
        maps, worlds, preserved, metadata, reached, related, resultPost⟩
      simpa only [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore trace] using
        (CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop Staging.Recursive.Size.ForItems.empty trace)
  | @initializerUninitialized context nextContext scope binder rest body payload test post statements expected type mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.let_tail
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih ⟨tailShape, shape.2⟩ (InitializerTyping.absent sourceTyped extended) projection (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], outcome.restore environment, after, finalMap, finalWorld,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_absent mono extended .append trace,
        (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions represented), finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest test post statements expected type mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.let_tail
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
          exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [initialSourceSize]], _, middle, middleMap, middleWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono initialTrace, .fault matched,
            middleHeaps, maps, worlds, preservation, metadata, middleState, expressionRelated, initialPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          have frameRead := (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
          obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
              nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, reached, allocationRelated, nextAdmitted⟩ :=
            CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer.toOrdinary
              mono extended ordinary allocation annotation same (sourceType ▸ initialPost.at_value.1) (sourceType ▸ payload)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
              reference frameRead Dynamic.Heap.Allocates.append middleState ((acquire _ _ conditioned) middleState frameRead)
              initialPost.at_value.2
          obtain ⟨branchSize, branchSmaller, branchEval⟩ := completed.bind_success initialEval.sound
          obtain ⟨tailSize, smaller, tailEval⟩ := branchEval.let_body allocationEval
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, related,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, tailState, tailRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.initialized sourceTyped mono extended) projection (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], outcome.restore environment, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_initialized mono extended initialTrace .append trace,
            (CallableIndexedOwnedAdmittedStagedImperativePositions.represents_restore functions related), finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact CallableIndexedOwnedAdmittedStagedImperativePositions.post_restore bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @initializerDiscard context scope expression expressionNode rest lowered body test post statements expected type expressionFound child remaining remainingErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      have tailShape := shape.1.discard_tail
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
          exact ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [sourceSize]], _, middle, middleMap, middleWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ (InitializerTyping.expression sourceTyped) projection (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], outcome, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_expression childTrace tailTrace, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @initializerAssign context scope assignment operator rhs rest body test post statements expected type head remaining remainingErrors headErrors ih =>
      intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed
      obtain ⟨rfl, bare, tailShape⟩ := shape.1.assign_tail
      have assignmentTyped := (InitializerTyping.assignment sourceTyped).1
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
        head bare environments heaps locals agrees actualTyped initial admitted graph.nodeOccurrencesUnique assignmentTyped
        budget typedChildren completed within
      cases result with
      | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [_]], _, _, _, _,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot trace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
          exact fault_post bridge reached stable
      | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (InitializerTyping.assignment sourceTyped).2
          obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih ⟨tailShape, shape.2⟩ tailTyped projection (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], outcome, after, finalMap, finalWorld,
            CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_assignment snapshot childTrace write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | initializerBitNot =>
      intro shape sourceTyped projection
      cases shape.1

include bridge bindings definitions registered producer acquire transport extension in
theorem reflects_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (graph : OccurrenceGraphWellFormed invocation.source)
    {expressionSyntax : ExpressionId → Prop} {administrative : Core.Context}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source expressionSyntax (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative context scope position expected type code)
    {diagnosticPolicy : AssignmentDiagnosticPolicy} {catalogRegistry : SourceCoreRawMetadata.Registry}
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : Tree.CatalogSites diagnosticPolicy catalogRegistry catalogFaults tree)
    {mode : Bool} {statements : List StatementId}
    (atStatements : position = .statements mode statements)
    (shape : Shape invocation.source mode statements)
    (sourceTyped : ProtectedStateImperativeTypedSourceSites.Statements invocation.source context statements)
    (projection : compiled.compatible.checked.catalog.project expected = .ok type)
    {size : Nat} (within : size ≤ budget)
    {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
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
      Staging.Recursive.Size.StatementsIn program stages mode sourceSize invocation context environment before
        statements finalContext outcome after ∧
      Represents model finalMap finalWorld mode expected type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected outcome reached := by
  cases atStatements
  exact reflects_position bridge bindings transport functions extension definitions registered producer condition acquire
    children graph tree catalogSites shape sourceTyped projection within
    environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativeFlow
