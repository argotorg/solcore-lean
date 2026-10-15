import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerProjectedSource
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedResolutionLifting

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
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
/-- Ordered keys, getter, RHS and real write are lifted at their actual states. -/
theorem assignProjected {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignValue assignment operator rhs :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
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
    rcases SelectedCompilationStageForInitialInversion.assignProjected trace with
      ⟨assignedSize, reason, strict, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_root_fault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_getter_fault projected measuredKeys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_write_fault projected measuredKeys snapshot measuredRhs (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CallableIndexedOwnedAdmittedStagedProjectedAssignmentHeads.preserves_value
                (values := .initial compiled.compatible.checked)
                (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => preservation n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextSize, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (Nat.le_trans (Nat.le_of_lt tailStrict) within)
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
                ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
                (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
                middleState, conditioned, nextAdmitted⟩ tail
            exact ⟨_, result, finalHeap,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment
                projected measuredKeys snapshot measuredRhs write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
