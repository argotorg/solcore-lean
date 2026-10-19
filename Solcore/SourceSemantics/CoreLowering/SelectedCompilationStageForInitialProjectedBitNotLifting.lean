import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedBitNotInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedBitNotSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotPreservation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreCompatibleDataPlaces DataPlaceExecution DataPatternValues
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions



include bridge functions faithful observations condition transport extension in
/-- Ordered keys, getter and unary write are lifted at their actual states. -/
theorem bitNotProjected {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignBitNot assignment :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  have targetTyped : SourcePlaceHasType invocation.source context assignment.target .word := by
    cases assignmentTyped with | intro typed _ => exact typed
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  let layout := head.layout
  have ordinary := head.ordinary
  have keyTyped := CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
  have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
      (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
        environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
    SelectedCompilationStageProjectedResolutionLifting.lifts
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
      bridge functions extension transport
      faithful observations budget layout ordinary unique originalKeyTyped children preservation
      environments heaps locals agrees actualTyped initial admitted head.slot head.writable resolved bounded
  rcases SelectedCompilationStageForInitialInversion.bitNotProjected trace with
    ⟨assignedSize, reason, strict, rfl, failed⟩ |
    ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
  · cases failed with
    | target failed =>
      rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
        ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
        ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
      · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_root_fault projected rootFault, .completed (.fault reason)⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_getter_fault projected measuredKeys getterFault, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
              cases getterFault <;> exact .intro (by assumption) (by assumption)
            obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
    | uninitialized resolved empty =>
      rcases liftResolved resolved
        (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
        ⟨origin, call, reason, reached, ready, keys⟩ |
        ⟨sources, keys, snapshot, keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
      ·
        obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
        exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      · obtain ⟨replacement, native, represented, applies, _, _⟩ :=
          CompatiblePlaceNumericBitNotModifier.success head.profile resolution.snapshotRelated
            (environment := rhsEnvironment head.prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) .unit actual) (rhs := .var 0) (.var (index := 1) rfl)
            (binaryOperator (head.prepared.route.leafType = .integer) .equal) resolution.store head.invalid
        have sourceApplies := resolution.selectedEq.symm ▸ applies
        rw [empty] at sourceApplies
        cases sourceApplies
    | operand resolved selected invalid =>
      rcases liftResolved resolved
        (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
        ⟨origin, call, reason, reached, ready, keys⟩ |
        ⟨sources, keys, snapshot, keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
      ·
        obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
        exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      · obtain ⟨replacement, native, represented, applies, _, _⟩ :=
          CompatiblePlaceNumericBitNotModifier.success head.profile resolution.snapshotRelated
            (environment := rhsEnvironment head.prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) .unit actual) (rhs := .var 0) (.var (index := 1) rfl)
            (binaryOperator (head.prepared.route.leafType = .integer) .equal) resolution.store head.invalid
        have sourceApplies := resolution.selectedEq.symm ▸ applies
        rw [selected] at sourceApplies
        cases sourceApplies with
        | word value => exact (invalid.excludes_application ⟨_, .wordBitNot value⟩).elim
        | integer value => exact (invalid.excludes_application ⟨_, .integerBitNot value⟩).elim
  · cases assigned with
    | intro resolved write =>
      rcases liftResolved resolved
        (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
        ⟨origin, call, reason, reached, ready, keys⟩ |
        ⟨sources, keys, snapshot, keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
      · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
        exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_bitNot_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      ·
        obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
        obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
            _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
          CallableIndexedOwnedAdmittedStagedProjectedBitNotHeads.preserves_value
            (values := .initial compiled.compatible.checked)
            (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
            bridge functions extension transport
            faithful observations head projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
            (keyStageSize + 1) (fun n _ => preservation n)
            measuredKeys (by omega) snapshot write
        obtain ⟨nextSize, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, environments.extend maps worlds, middleHeaps,
            locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
            ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
            (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
            middleState, conditioned, nextAdmitted⟩ tail
        exact ⟨_, result, finalHeap,
          CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_bitNot
            projected measuredKeys snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
