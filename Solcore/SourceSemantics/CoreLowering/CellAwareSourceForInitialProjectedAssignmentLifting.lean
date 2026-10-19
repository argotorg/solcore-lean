import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceProjectedResolutionLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension faithful observations in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  let budget := size + 1
  have within : size ≤ budget := by omega
  have childLift : ∀ childSize, childSize < budget → CellAwareScopeSourceLiftBounds.LiftsAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate childSize := fun childSize _ => children runtime covers sameLedger childSize
  have childMeaning : ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt bridge context
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      named stages invocation certificate faults childSize := preservation runtime covers sameLedger
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨targetType, targetTyped⟩ := CallableIndexedOwnedPlaceAdmission.assignment_target_typed assignmentTyped
  obtain ⟨originalTypes, originalKeyTyped⟩ := CallableIndexedOwnedPlaceAdmission.place_keys_typed targetTyped
  rcases head with ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, shape, slot, writable, rhsFound, generated, rightView, rightType, profile⟩
  cases shape with
  | bare empty _ => exact (projected empty).elim
  | @projected codes leaf sourceTypes site layout ordinary =>
    let head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
        certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs :=
      ⟨prepared, index, codes, leaf, lowered, rhsNode, invalid, .projected layout ordinary,
        slot, writable, rhsFound, generated, rightView, rightType, profile⟩
    have keyTyped := CellAwareScopeProjectedAssignmentHeads.tree_typed layout.children unique originalKeyTyped
    have liftResolved {resolvedTarget : Dynamic.ResolvedPlace} {resolvedHeap : Dynamic.Heap} {resolvedGrade : Nat}
        (resolved : SourceExecutionSize.SourcePlaceResolves program resolvedGrade context invocation.evidence invocation.source
          environment before assignment.target resolvedTarget resolvedHeap) (bounded : resolvedGrade ≤ budget) :=
      CellAwareSourceProjectedResolutionLifting.lifts
                (stages := stages) (faults := faults)
        bridge functions extension transport
        faithful observations budget layout ordinary unique originalKeyTyped childLift childMeaning
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation head.slot head.writable resolved bounded
    rcases SelectedCompilationStageForInitialInversion.assignProjected trace with
      ⟨assignedSize, reason, strict, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_root_fault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
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
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
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
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.fault evaluated)
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
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
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
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
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
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
          exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_keys_fault projected ready measuredKeys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              obtain ⟨keyGrade, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
              obtain ⟨rhsGrade, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
              exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.projected_rhs_fault projected measuredKeys snapshot measuredRhs, .rejected origin call reason _ reached⟩
          | completed =>
            obtain ⟨keyStageSize, measuredKeys⟩ := Staging.Recursive.Size.Expressions.of_trace keys
            obtain ⟨rhsStageSize, measuredRhs⟩ := Staging.Recursive.Size.Expression.of_trace lifted
            obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
                effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
              CellAwareScopeProjectedAssignmentHeads.preserves_value
                                (stages := stages) (faults := faults)
                bridge functions extension transport
                faithful observations head projected environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
                (keyStageSize + rhsStageSize + 1) (fun n _ => childMeaning n)
                measuredKeys (by omega) snapshot measuredRhs (by omega) write
            obtain ⟨nextSize, result, finalHeap, restTrace, restAdapted⟩ := remaining
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped,
                runtime, covers, sameLedger, middleState, nextAdmitted,
                authority.transport effect, physical.transport effect framePreserved, owner, sameLocation, ready⟩ tail
            exact ⟨_, result, finalHeap,
              CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_projected_assignment
                projected measuredKeys snapshot measuredRhs write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
