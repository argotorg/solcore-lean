import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeProjectedAssignmentPreservation
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceProjectedResolutionLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedAssignmentInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! Independent projected assignment lifts the actual ordered keys, getter,
RHS and final write at their reached mixed states. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

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

include transport extension faithful observations in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
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
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
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
    rcases SelectedCompilationStageProjectedAssignmentInversion.child_and_tail unique found form trace with
      ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, .assignProjectedRootFault (lookupStatement?_sound found) form projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.fault bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareScopeSourceSequenceLifting.values bridge budget
            layout.children unique keyTyped childLift childMeaning environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .assignProjectedGetterFault (lookupStatement?_sound found) form projected keys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .assignProjectedWriteFault (lookupStatement?_sound found) form projected keys snapshot lifted (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .assignProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := childLift _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (authority.transport resolution.effect)
              (physical.transport resolution.effect resolution.frame) owner sameLocation (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .assignProjectedRhsFault (lookupStatement?_sound found) form projected keys snapshot lifted, .rejected origin call reason _ reached⟩
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
            obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (environments.extend maps worlds) middleHeaps
              (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped runtime covers sameLedger suffix
              middleState nextAdmitted (authority.transport effect) (physical.transport effect framePreserved)
              owner sameLocation ready tail
            exact ⟨nextContext, result, finalHeap,
              .assignProjected (lookupStatement?_sound found) form projected keys snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowProjectedAssignmentLifting
