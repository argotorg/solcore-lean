import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBlockSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedWhileSequences
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativeFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion

/-! Scoped compiler statements include conditionals, finite while loops, bare plain assignment,
lexical allocation, discard and return. Strict child bounds run the original recursive
Source relation; writes target the actual heap reached by the RHS. -/
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
open CallableIndexedOwnedPreparedStagedBranchingTree (Shape)
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
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
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

include bridge bindings definitions registered producer acquire transport extension in
/-- Preservation follows the original staged Source children and allocation.
Lexical restoration preserves the returned value's captured cells and the
same native store; it changes only the caller's lexical observations. -/
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
  induction tree generalizing mode statements size mapping world actualContext environment canonical actual before
      store ξ contextLocation native finalContext outcome after with
  | @body context scope mode statements expected type code syntaxTree body =>
      cases atStatements
      exact CallableIndexedOwnedAdmittedStagedScopedLexicalPreservation.preserves bridge bindings functions definitions registered producer condition acquire children unique
        body shape projection within environments heaps locals agrees actualTyped
        reference read unmapped initial conditioned admitted trace
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail ih =>
      cases atStatements
      have tailShape := shape.tail_of_let found form
      obtain ⟨tailSize, location, bound, sameSize, allocated, remainingTrace⟩ :=
        CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.absent unique found form extended trace
      have tailWithin : tailSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
        rw [sameSize]; exact Staging.Recursive.Size.child_lt_stepSize (by simp))) within
      obtain ⟨captured, _captures, _capturedTyped, allocationEval, nextEnvironments, nextHeaps, nextLocals,
          nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, allocatedRelated, nextAdmitted⟩ :=
        CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
          mono extended ordinary projected allocation annotation same environments heaps locals agrees actualTyped
          reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
      obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented,
          finalHeaps, maps, worlds, finalFrame, metadata, tailState, tailRelated, post⟩ :=
        ih rfl tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining ih =>
      cases atStatements
      have tailShape := shape.tail_of_let found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := child
      have nodeEq := Option.some.inj (initialFound.symm.trans typedFound)
      cases nodeEq
      rw [sequence_rename]
      rcases CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.initialized unique found form extended trace with
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
              ih rfl tailShape (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection tailWithin nextEnvironments nextHeaps nextLocals nextAgrees nextTyped
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
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining ih =>
      cases atStatements
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
              ih rfl tailShape (ProtectedStateImperativeStatementSuffixTyping.discard unique sourceTyped found form) projection tailWithin (environments.extend firstMaps firstWorlds)
                middleHeaps (locals.mono firstMetadata) (GenericExpressionMeaning.agree_prefix agrees coreValue)
                (.cons payload.runtime_hasType (actualTyped.weaken firstWorlds)) reference
                ((firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
                (firstFrame contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
                middleState conditioned firstPost.at_value.2 remainingTrace
            rw [GenericExpressionMeaning.rename_prefix] at second
            exact ⟨value, finalStore, finalMap, finalWorld, LocalSequence.discard_success _ first second,
              related, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans preservation,
              firstMetadata.trans metadata, reached, callerProtocol.trans expressionRelated tailRelated, post⟩
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining ih =>
      cases atStatements
      obtain ⟨rfl, bare, tailShape⟩ := shape.assign_tail found form
      have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
        (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
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
      rcases CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion.child_and_tail unique found form snapshot trace with
        ⟨childSize, failure, sameSize, contextEq, outcomeEq, childTrace⟩ |
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
          ih rfl tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form)
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
  | block found form inner remaining innerIH remainingIH =>
      cases atStatements
      obtain ⟨innerShape, restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
      have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (innerIH rfl innerShape innerTyped projection)
        unique found form (.inl (remainingIH rfl restShape restTyped projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining thenIH elseIH remainingIH =>
      cases atStatements
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
        (thenIH rfl leftShape leftTyped projection) (elseIH rfl rightShape rightTyped projection)
        unique found form (.inl (remainingIH rfl restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix unique sourceTyped found form) projection)) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | terminalBlock exactUnique found form inner stops issued ih =>
      cases atStatements
      obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
      have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedBlockSequences.preserves bridge functions condition
        (ih rfl innerShape innerTyped projection)
        unique found form (.inr stops) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | terminalIf exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenIH elseIH =>
      cases atStatements
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
        (thenIH rfl leftShape leftTyped projection) (elseIH rfl rightShape rightTyped projection)
        unique found form (.inr ⟨thenStops, elseStops⟩) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | whileLoop found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopIH remainingIH =>
      cases atStatements
      obtain ⟨loopShape, restShape⟩ := shape.loop found form
      obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
      have same := Option.some.inj (conditionFound.symm.trans typedFound)
      cases same
      have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children unique sourceTyped found form).2
      have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix unique sourceTyped found form
      exact CallableIndexedOwnedAdmittedStagedWhileSequences.preserves bridge functions condition transport
        (children _) conditionFound conditionType typed certified nativeTyped
        (loopIH rfl loopShape loopTyped projection)
        unique found form (remainingIH rfl restShape restTyped projection) within
        environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | breaking found form | continuing found form
  | bitNot found form _ _ _ | forLoop found form _ _ _ _
  | matchWith found form _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | terminalMatch _ found form _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      cases atStatements
      have impossible := shape.head_allowed found
      simp only [form, CallableIndexedOwnedPreparedStagedBranchingTree.allowedForm, Bool.false_eq_true] at impossible
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard | initializerAssign | initializerBitNot =>
      cases atStatements

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation
