import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotReflection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedAssignmentReflection
import Solcore.SourceSemantics.CoreLowering.PreparedAssignmentReachedDiagnostics
import Solcore.SourceSemantics.Staging.RecursiveProjectedTargetFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForPostContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalTree
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderPost

/-! Actual completed post-header code determines its staged item trace and
restores the outer caller while retaining all allocations and capture writes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
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
  (functionTypes : FunctionRuntimeViews functions)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
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
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (diagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions callerProtocol invocation.source
    invalidProjection missingDefault receiving (fun reason token => faults (.semantic reason) token))

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

include bridge bindings definitions registered producer acquire transport extension functionTypes faithful observations diagnostics in
/-- Native completion determines the actual ordered lexical Source trace,
including the distinct context after successful allocation and initializer
faults before allocation. The returned caller state retains the entire heap. -/
theorem reflects_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      ReflectsAt bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    {catalogFaults : FunctionCalls.FaultRep}
    (catalogSites : PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault receiving catalogFaults tree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items)
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
      Staging.Recursive.Size.ForItems program stages sourceSize invocation context environment before
        items finalContext outcome after ∧
      Represents model finalMap finalWorld false expected type faults (restoredOutcome environment outcome) value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ Post bridge context expected (restoredOutcome environment outcome) reached := by
  induction catalogSites generalizing size mapping world actualContext environment canonical actual before
      store finalStore ξ contextLocation native value with
  | @nil context scope code next =>
      change code = LocalLoop.fallthrough type at next
      subst code
      rw [LoopRenaming.fallthrough] at completed
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound (LocalLoop.fallthrough_evaluates type actual store)
      exact ⟨_, context, .done environment, before, mapping, world, .empty,
        .fallthrough environment (.inl rfl), heaps, .refl _, .refl _, .refl _ _, .refl _,
        initial, callerProtocol.refl initial, admitted⟩
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail tailSites ih =>
      have tailShape := shape.let_tail
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer.toOrdinary
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read Dynamic.Heap.Allocates.append initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨tailSize, smaller, continuation⟩ := completed.let_body allocationEval
      obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended) (Nat.le_trans (Nat.le_of_lt smaller) within)
          nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
          (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          reached conditioned nextAdmitted continuation
      let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
        (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState
      refine ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
        .absent mono extended .append trace,
        (rep_environment functions represented), finalHeaps, (show LocationMap.Extends mapping (mapping ++ [store.length + 2]) from ⟨_, rfl⟩).trans maps,
        (show WorldExtends world (world ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType payload]) from ⟨_, rfl⟩).trans worlds,
        preservation.trans finalFrame, (Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans metadata,
        finalState, callerProtocol.trans allocatedRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState)), ?_⟩
      exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := payload) (value := .cellRef (OptionalCell.cellType payload) (store.length + 2)) tailState post)
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary initialFound sourceType child allocation annotation same remaining tailSites ih =>
      have tailShape := shape.let_tail
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
            .initializerFault mono initialTrace, .fault matched,
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
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended) (Nat.le_trans (Nat.le_of_lt (Nat.lt_trans smaller branchSmaller)) within)
              nextEnvironments nextHeaps nextLocals nextAgrees nextTyped nextReference nextRead
              (allocationFrame contextLocation (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                (List.getElem?_eq_some_iff.mp frameRead).1).1 reached conditioned nextAdmitted tailEval
          let finalState := bindings.restore (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
            (id := binder.id) (type := lowered.type)
            (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState
          refine ⟨Staging.Recursive.Size.stepSize [initialSourceSize, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .initialized mono extended initialTrace .append trace,
            (rep_environment functions related), finalHeaps,
            maps.trans ((show LocationMap.Extends middleMap (middleMap ++ [middleStore.length + 2]) from ⟨_, rfl⟩).trans finalMaps),
            worlds.trans ((show WorldExtends middleWorld (middleWorld ++ [frame.type, allocation.entry.layout.type, OptionalCell.cellType lowered.type]) from ⟨_, rfl⟩).trans finalWorlds),
            preservation.trans (allocationFrame.trans finalFrame),
            metadata.trans ((Dynamic.HeapMetadataExtend.of_allocation Dynamic.Heap.Allocates.append).trans finalMetadata),
            finalState, callerProtocol.trans expressionRelated
              (callerProtocol.trans allocationRelated (callerProtocol.trans tailRelated (bindings.restore_related (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (id := binder.id) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState))), ?_⟩
          exact post_environment bridge (restore_post bindings extended (index := ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) (type := lowered.type) (value := .cellRef (OptionalCell.cellType lowered.type) (middleStore.length + 2)) tailState post)
  | @discard context scope expression expressionNode rest lowered body expressionFound child remaining tailSites ih =>
      have tailShape := shape.discard_tail
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
            .expressionFailure childTrace, .fault matched, middleHeaps,
            firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, expressionRelated, firstPost.at_fault_type⟩
      | @value sourceValue coreValue payload =>
          obtain ⟨tailSize, tailSmaller, tailEvaluation⟩ := completed.bind_success childEvaluation.sound
          obtain ⟨tailSourceSize, finalContext, outcome, after, finalMap, finalWorld, tailTrace, related,
              finalHeaps, maps, worlds, preservation, metadata, reached, tailRelated, post⟩ :=
            ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped) (Nat.le_trans (Nat.le_of_lt tailSmaller) within)
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (GenericExpressionMeaning.agree_prefix agrees coreValue)
              (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
              ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              middleState conditioned firstPost.at_value.2
              (by simpa only [GenericExpressionMeaning.rename_prefix] using tailEvaluation)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize, tailSourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .expression childTrace tailTrace, related, finalHeaps,
            firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation, firstMetadata.trans metadata,
            reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope assignment operator rhs rest body head remaining tailSites headErrors ih =>
      have invalidToken : AssignmentOperandDiagnostics.OperandsLaw
          (fun reason token => faults (.semantic reason) token) operator head.invalid := PreparedAssignmentReachedDiagnostics.operands headErrors semantic
      obtain ⟨_profile, tailShape⟩ := shape.assignment_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      by_cases bare : assignment.target.projections = []
      · have result := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative) bridge functions extension transport
          head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          budget typedChildren invalidToken completed within
        cases result with
        | fault snapshot trace same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignmentFailure snapshot trace, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge reached stable
        | operands snapshot trace currentRead rootType initialized path invalid same matched finalHeaps maps worlds preservation metadata reached related stable =>
            cases same
            refine ⟨Staging.Recursive.Size.stepSize [_], context, _, _, _, _,
              .assignmentOperands snapshot trace currentRead rootType initialized path invalid, .fault matched,
              finalHeaps, maps, worlds, preservation, metadata, reached, related, ?_⟩
            exact fault_post bridge (context := context) (expected := expected)
              (failure := .semantic (.invalidAssignmentOperands operator)) reached stable
        | success snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
            have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2
            obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
                finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
              ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
                (environments.extend maps worlds) middleHeaps (locals.mono metadata)
                (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
                ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                reached conditioned nextAdmitted
                (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
            exact ⟨Staging.Recursive.Size.stepSize [_, sourceSize], finalContext, outcome, after, finalMap, finalWorld,
              .assignment snapshot childTrace write trace, represented,
              finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
              metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
      · have errors := PreparedAssignmentReachedDiagnostics.shape_errors (environment := environment) headErrors semantic diagnostics assignmentTyped initial
        have result := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.reflects_bounded
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport faithful observations head bare
          environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          budget typedChildren functionTypes errors completed within
        cases result with
        | keyFault ready keysTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentKeysFault bare ready keysTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | getterFault keysTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentGetterFault bare keysTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | rhsFault keysTrace snapshot childTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentRhsFault bare keysTrace snapshot childTrace, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
        | writeFault keysTrace snapshot childTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
          cases same
          exact ⟨_, context, _, _, _, _, .projectedAssignmentWriteFault bare keysTrace snapshot childTrace failed, .fault matched,
            finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
        | success keysTrace snapshot childTrace write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
            .projectedAssignment bare keysTrace snapshot childTrace write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩
  | @bitNot context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_profile, bare, tailShape⟩ := shape.bitNot_tail head.bare
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      have result := CallableIndexedOwnedAdmittedStagedBareBitNotHeads.reflects_bounded (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative) bridge functions transport
        head environments heaps locals agrees actualTyped initial admitted assignmentTyped headErrors completed
      cases result with
      | fault trace same matched finalHeaps maps worlds preservation reached related stable =>
          cases same
          refine ⟨Staging.Recursive.Size.stepSize [], context, _, _, _, _,
            .bitNotFault head.bare trace, .fault (semantic _ _ matched),
            finalHeaps, maps, worlds, preservation, .refl _, reached, related, ?_⟩
          exact fault_post bridge (context := context) (expected := expected)
            (failure := .semantic _) reached stable
      | success snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
          have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2
          obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
              finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
            ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
              (environments.extend maps worlds) middleHeaps (locals.mono metadata)
              (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
              ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
              (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
              reached conditioned nextAdmitted
              (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
          exact ⟨Staging.Recursive.Size.stepSize [sourceSize], finalContext, outcome, after, finalMap, finalWorld,
            .bitNot snapshot write trace, represented,
            finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
            metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩

  | @bitNotProjected context scope assignment rest body head remaining tailSites headErrors ih =>
      obtain ⟨_profile, tailShape⟩ := shape.unary_tail
      have assignmentTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
        cases assignmentTyped with | intro typed _ => exact typed
      have errors := PreparedAssignmentReachedDiagnostics.unary_errors (environment := environment)
        headErrors diagnostics targetTyped initial
      have typedChildren : ReflectsBelow bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults budget := by
        intro size smaller scope id lowered generated node found typed
        obtain ⟨node, nodeFound, nodeTyped, certified⟩ := generated
        exact children context size smaller certified found typed
      have result := CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.reflects_bounded
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        bridge functions extension transport faithful observations head head.projected
        environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
        budget typedChildren functionTypes errors completed within
      cases result with
      | keyFault ready keysTrace same matched finalHeaps maps worlds preservation metadata reached related stable =>
        cases same
        exact ⟨_, context, _, _, _, _, .projectedBitNotKeysFault head.projected ready keysTrace, .fault matched,
          finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge reached stable⟩
      | getterFault keysTrace failed same matched finalHeaps maps worlds preservation metadata reached related stable =>
        cases same
        exact ⟨_, context, _, _, _, _, .projectedBitNotGetterFault head.projected keysTrace failed, .fault matched,
          finalHeaps, maps, worlds, preservation, metadata, reached, related, fault_post bridge (context := context) (expected := expected) (failure := .semantic _) reached stable⟩
      | success keysTrace snapshot write middleHeaps maps worlds preservation metadata count typed reached related nextAdmitted strict remaining =>
        have tailTyped := (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2
        obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented,
            finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata, last, lastRelated, post⟩ :=
          ih tailShape tailTyped (Nat.le_trans (Nat.le_of_lt strict) within)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata)
            (DataPlaceChildExpressions.prefix_agrees agrees _) typed reference
            ((preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
            (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
            reached conditioned nextAdmitted
            (by simpa only [DataPlaceChildExpressions.rename_prefix, count, SourceCoreCompatibleDataPlaces.shift, SourceCoreDataPlaces.shift] using remaining)
        exact ⟨_, finalContext, outcome, after, finalMap, finalWorld,
          .projectedBitNot head.projected keysTrace snapshot write trace, represented,
          finalHeaps, maps.trans finalMaps, worlds.trans finalWorlds, preservation.trans finalFrame,
          metadata.trans finalMetadata, last, callerProtocol.trans related lastRelated, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderReflection
