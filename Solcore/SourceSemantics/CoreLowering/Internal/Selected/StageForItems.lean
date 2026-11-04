import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageBitNot
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProjectedBitNotPreservation
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForLoops
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedLexicalAllocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeaderPreservation
import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageWhileMatch
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedScopedImperativePreservation

/-!
# Lifting to staged Source: for headers

Lifting of `for` headers, initializers and items, by the form of each item: assignments, bit-not updates, discards and lexical items.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedAssignmentLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
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
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignValue assignment operator rhs :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
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
    rcases SelectedCompilationStageProjectedAssignmentInversion.item_and_tail trace with
      ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
      ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
    · cases failed with
      | target failed =>
        rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
          ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
          ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
        · exact ⟨_, _, _, .projectedAssignmentRootFault projected rootFault, .completed (.fault reason)⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
            layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
            (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
          have keys := lifted
          rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
          cases adapted with
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentGetterFault projected keys getterFault, .completed (.fault reason)⟩
          | rejected origin call reason reached =>
              have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
                cases getterFault <;> exact .intro (by assumption) (by assumption)
              exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
      | rhs resolved evaluated =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.fault evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .completed (.fault reason)⟩
      | operands resolved evaluated currentRead rootType initialValue pathRead invalid =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentWriteFault projected keys snapshot lifted (.operands currentRead rootType initialValue pathRead invalid), .completed (.fault (.invalidAssignmentOperands operator))⟩
      | structuralUpdate resolved evaluated currentRead rootType initialValue pathFault =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
          | completed =>
              exact ⟨_, _, _, .projectedAssignmentWriteFault projected keys snapshot lifted (.structural currentRead rootType initialValue pathFault), .completed (.fault reason)⟩
    · cases assigned with
      | intro resolved evaluated write =>
        rcases liftResolved resolved
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
          ⟨origin, call, reason, reached, ready, keys⟩ |
          ⟨sources, keys, snapshot, _keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
        · exact ⟨_, _, _, .projectedAssignmentKeysFault projected ready keys, .rejected origin call reason _ reached⟩
        · obtain ⟨staged, reached, lifted, adapted⟩ := children _
            (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
            head.right head.found typed (environments.extend resolution.maps resolution.worlds)
            resolution.heaps (locals.mono resolution.metadata) agrees (actualTyped.weaken resolution.worlds)
            getterState getterAdmission (.value evaluated)
          cases adapted with
          | rejected origin call reason reached =>
              exact ⟨_, _, _, .projectedAssignmentRhsFault projected keys snapshot lifted, .rejected origin call reason _ reached⟩
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
            obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
              (Nat.le_trans (Nat.le_of_lt tailStrict) within)
              ⟨_, _, _, environments.extend maps worlds, middleHeaps,
                locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
                ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
                (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
                middleState, conditioned, nextAdmitted⟩ tail
            exact ⟨nextContext, result, finalHeap,
              .projectedAssignment projected keys snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedBitNotLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedBitNotLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreCompatibleDataPlaces DataPlaceExecution DataPatternValues
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
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
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignBitNot assignment :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
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
  rcases SelectedCompilationStageProjectedBitNotInversion.item_and_tail trace with
    ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
    ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
  · cases failed with
    | target failed =>
      rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
        ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
        ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
      · exact ⟨_, _, _, .projectedBitNotRootFault projected rootFault, .completed (.fault reason)⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .rejected origin call reason _ reached⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            exact ⟨_, _, _, .projectedBitNotGetterFault projected keys getterFault, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
              cases getterFault <;> exact .intro (by assumption) (by assumption)
            exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .rejected origin call reason _ reached⟩
    | uninitialized resolved empty =>
      rcases liftResolved resolved
        (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
        ⟨origin, call, reason, reached, ready, keys⟩ |
        ⟨sources, keys, snapshot, keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
      ·
        exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .rejected origin call reason _ reached⟩
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
        exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .rejected origin call reason _ reached⟩
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
      · exact ⟨_, _, _, .projectedBitNotKeysFault projected ready keys, .rejected origin call reason _ reached⟩
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
        obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, environments.extend maps worlds, middleHeaps,
            locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
            ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
            (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
            middleState, conditioned, nextAdmitted⟩ tail
        exact ⟨nextContext, result, finalHeap,
          .projectedBitNot projected keys snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsProjectedBitNotLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open GenericLexicalStatements
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

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


include bridge functions definitions registered producer acquire in
/-- The original absent allocation constructs the actual extended physical
state before the body suffix is lifted. -/
theorem absent {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest : List ForItemForm}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    {administrative : Core.Context}
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder none :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨tailSize, location, bound, strict, allocated, tail⟩ :=
    SelectedCompilationStageForItemsSourceInversion.absent mono extended trace
  obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, _allocatedRelated, nextAdmitted⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
  obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
    (Nat.le_trans (Nat.le_of_lt strict) within)
    ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      nextReference, nextRead, (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
      reached, conditioned, nextAdmitted⟩ tail
  exact ⟨resultContext, result, resultHeap,
    .absent mono extended allocated restTrace, restAdapted⟩

include bridge functions definitions registered producer acquire in
/-- The initializer reaches its own heap first. Its real represented value
then initializes the original binder before the suffix executes. -/
theorem initialized {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest : List ForItemForm}
    {binder : TypedBinder} {expression : ExpressionId}
    {expressionNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (sourceType : expressionNode.type = binder.scheme.body)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates context scope expression lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (children : ∀ childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    {administrative : Core.Context}
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder (some expression) :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForItemsSourceInversion.initialized mono extended trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, strict, tailStrict, evaluated, allocated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .initializerFault mono lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .initializerFault mono lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .initializerFault mono lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      cases represented with
      | value payload =>
        have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
            nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, nextState, _allocatedRelated, nextAdmitted⟩ :=
          CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
            mono extended ordinary allocation annotation same (sourceType ▸ post.at_value.1) (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) post.at_value.2
        obtain ⟨resultContext, result, resultHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            nextReference, nextRead, (allocationFrame contextLocation stillUnmapped (List.getElem?_eq_some_iff.mp frameRead).1).1,
            nextState, conditioned, nextAdmitted⟩ tail
        exact ⟨resultContext, result, resultHeap,
          .initialized mono extended lifted allocated restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsLexicalLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


theorem nil {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition [] budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageForItemsSourceInversion.nil trace
  exact ⟨_, .done environment, _, .empty, .completed (.fallthrough _)⟩

include bridge functions condition in
/-- A completed expression supplies the real next physical state before the
suffix is lifted. A rejected expression stops at its own reached heap. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.expression expression :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForItemsSourceInversion.discard trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, strict, tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFailure lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFailure lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees,
          actualTyped.weaken worlds, reference, frameRead, stillUnmapped, middleState, conditioned, post.at_value.2⟩ tail
      exact ⟨nextContext, result, finalHeap, .expression lifted restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsDiscardLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions



include bridge functions condition transport extension in
/-- Value assignment lifts the RHS at the original target snapshot. The
existing real write producer supplies the next physical state for the suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignValue assignment operator rhs :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative)
    functions extension head bare environments heaps locals agrees
  rcases SelectedCompilationStageForItemsAssignmentInversion.child_and_tail snapshot trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, strict, tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignmentOperands snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignmentFailure snapshot lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          (preservation stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps,
          locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
          ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
          (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
          middleState, conditioned, nextAdmitted⟩ tail
      exact ⟨nextContext, result, finalHeap,
        .assignment snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsAssignmentLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {faults : RecursiveStageMeaning.FaultRep}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions condition transport in
/-- The real unary write supplies the physical state for the suffix. -/
theorem lifts {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm} {assignment : AssignmentResolution}
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (remaining : ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest budget) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.assignBitNot assignment :: rest) budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready finalContext outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForItemsBitNotInversion.write_and_tail head.bare trace with
    ⟨reason, rfl, rfl, rfl, failed⟩ |
    ⟨tailSize, target, updated, written, tailStrict, snapshot, write, tail⟩
  · exact ⟨_, _, _, .bitNotFault head.bare failed, .completed (.fault reason)⟩
  · obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
        _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
      CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_value
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        bridge functions transport head environments heaps locals agrees actualTyped initial admitted assignmentTyped
        snapshot write
    obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
      (Nat.le_trans (Nat.le_of_lt tailStrict) within)
      ⟨_, _, _, environments.extend maps worlds, middleHeaps,
        locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
        ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
        (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
        middleState, conditioned, nextAdmitted⟩ tail
    exact ⟨nextContext, result, finalHeap, .bitNot snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForItemsBitNotLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageForLiftBounds
open CallableIndexedOwnedPreparedStagedLexicalTree (TypedCertificate)
open CallableIndexedOwnedPreparedStagedBranchingTree (ItemShape)
open GenericForHeader (Tree)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
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


variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)

include bridge functions faithful observations definitions registered producer acquire transport extension in
/-- Every actual post-header item preserves its ordered allocation, evaluation
and write. The loop caller restores its bindings only after this vector ends. -/
theorem lifts {budget : Nat}
    (children : ∀ context childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context childSize,
      CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
        bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {administrative : Core.Context} {control : ControlContext}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {type : Ty} {code : Expr}
    (tree : Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code)
    (shape : ItemShape items)
    (sourceTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context items) :
    ItemsLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition items budget := by
  revert shape sourceTyped
  induction tree with
  | nil next =>
    intro _ _
    exact SelectedCompilationStageForItemsDiscardLifting.nil bridge functions condition
  | @uninitialized context nextContext scope binder rest body payload mono extended ordinary projected allocation annotation same tail ih =>
    intro shape sourceTyped
    exact SelectedCompilationStageForItemsLexicalLifting.absent bridge functions definitions registered producer condition acquire
      mono extended ordinary projected allocation annotation same
      (ih shape.let_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.absent sourceTyped extended))
  | @initialized context nextContext scope binder initializer initializerNode lowered body rest mono extended ordinary found sourceType child allocation annotation same tail ih =>
    intro shape sourceTyped
    obtain ⟨node, nodeFound, typed, generated⟩ := child
    cases Option.some.inj (found.symm.trans nodeFound)
    exact SelectedCompilationStageForItemsLexicalLifting.initialized bridge functions definitions registered producer condition acquire
      mono extended ordinary found sourceType typed generated allocation annotation same (children context) (preservation context)
      (ih shape.let_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.initialized sourceTyped mono extended))
  | @discard context scope expression expressionNode rest lowered body found child tail ih =>
    intro shape sourceTyped
    obtain ⟨node, nodeFound, typed, generated⟩ := child
    cases Option.some.inj (found.symm.trans nodeFound)
    exact SelectedCompilationStageForItemsDiscardLifting.lifts bridge functions condition found typed generated
      (children context) (preservation context)
      (ih shape.discard_tail (CallableIndexedOwnedPreparedStagedForItemsTyping.expression sourceTyped))
  | @assign context scope assignment operator rhs rest body head tail ih =>
    intro shape sourceTyped
    obtain ⟨_profile, tailShape⟩ := shape.assignment_tail
    have typedChildren (size : Nat) (smaller : size < budget) :
        LiftsAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact children context size smaller certified found typed
    have typedPreservation (size : Nat) :
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact preservation context size certified found typed
    intro size within
    by_cases bare : assignment.target.projections = []
    · exact SelectedCompilationStageForItemsAssignmentLifting.lifts bridge functions transport extension condition
        unique head bare (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
        typedChildren typedPreservation
        (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2) within
    · exact SelectedCompilationStageForItemsProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension condition
        unique head bare (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).1
        typedChildren typedPreservation
        (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.assignment sourceTyped).2) within
  | @bitNot context scope assignment rest body head tail ih =>
    intro shape sourceTyped
    obtain ⟨_rawWord, _bare, tailShape⟩ := shape.bitNot_tail head.bare
    exact SelectedCompilationStageForItemsBitNotLifting.lifts bridge functions transport condition
      head (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2)

  | @bitNotProjected context scope assignment rest body head tail ih =>
    intro shape sourceTyped
    obtain ⟨_rawWord, tailShape⟩ := shape.unary_tail
    have typedChildren (size : Nat) (smaller : size < budget) :
        LiftsAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact children context size smaller certified found typed
    have typedPreservation (size : Nat) :
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt bridge context model stages invocation
          (TypedCertificate invocation.source certificates context) faults size := by
      intro scope id lowered generated node found typed
      obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
      exact preservation context size certified found typed
    intro size within
    exact SelectedCompilationStageForItemsProjectedBitNotLifting.lifts bridge functions faithful observations transport extension condition
      unique head head.projected (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).1
      typedChildren typedPreservation
      (ih tailShape (CallableIndexedOwnedPreparedStagedForItemsTyping.bitNot sourceTyped).2) within

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForHeaderLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedAllocationCompletion
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageForLiftBounds SelectedCompilationStageForInitialBounds
open GenericLexicalStatements
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

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


private theorem restore_adapted {outer inner : SourceSemantics.Context}
    (environment : Dynamic.Environment) {plain : Dynamic.ControlOutcome} {staged : Staging.Recursive.BodyOutcome}
    {after reached : Dynamic.Heap}
    (adapted : BodyAdapted inner plain after inner staged reached) :
    BodyAdapted outer (Dynamic.restoreControl environment plain) after outer (staged.restore environment) reached := by
  cases adapted with
  | completed matched => cases matched <;> exact .completed (by constructor)
  | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

include bridge functions definitions registered producer acquire in
/-- The original absent allocation constructs the actual extended physical
state before the body suffix is lifted. -/
theorem absent {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {binder : TypedBinder} {payload : Ty}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (projection : compiled.compatible.checked.catalog.project binder.scheme.body = .ok payload)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (absentRequest invocation.source scope binder payload))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (absentRequest invocation.source scope binder payload))
    (same : annotation.original = allocation.expression)
    {administrative : Core.Context}
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, payload) :: scope)) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder none :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨tailSize, location, bound, nextOutcome, strict, sameOutcome, allocated, tail⟩ :=
    SelectedCompilationStageForInitialInversion.absent mono extended trace
  subst outcome
  obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
      nextAgrees, nextTyped, nextReference, nextRead, preservation, reached, _allocatedRelated, nextAdmitted⟩ :=
    CallableIndexedOwnedAdmittedLexicalAllocation.allocate_absent bridge functions definitions registered producer
      mono extended ordinary projection allocation annotation same environments heaps locals agrees actualTyped
      reference read allocated initial ((acquire _ _ conditioned) initial read) admitted
  obtain ⟨_, _, resultHeap, restTrace, restAdapted⟩ := remaining
    (Nat.le_trans (Nat.le_of_lt strict) within)
    ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
      nextReference, nextRead, (preservation contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
      reached, conditioned, nextAdmitted⟩ tail
  exact ⟨_, _, resultHeap,
    CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_absent mono extended allocated restTrace, restore_adapted environment restAdapted⟩

include bridge functions definitions registered producer acquire in
/-- The initializer reaches its own heap first. Its real represented value
then initializes the original binder before the suffix executes. -/
theorem initialized {budget : Nat} {context nextContext : SourceSemantics.Context}
    {scope : SourceCoreLocalCell.Scope} {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {binder : TypedBinder} {expression : ExpressionId}
    {expressionNode : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (ordinary : invocation.source.inputs.any (fun input => decide (input.id = binder.id)) = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (sourceType : expressionNode.type = binder.scheme.body)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates context scope expression lowered)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active (initializedRequest invocation.source scope binder lowered.type))
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated frame globals
      (layouts.allocatorAt owner active onError) (initializedRequest invocation.source scope binder lowered.type))
    (same : annotation.original = allocation.expression)
    (children : ∀ childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    {administrative : Core.Context}
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := nextContext) (scope := ((binder.id, lowered.type) :: scope)) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.letDecl binder (some expression) :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForInitialInversion.initialized mono extended trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, location, bound, nextOutcome, strict, tailStrict, sameOutcome, evaluated, allocated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .rejected origin call reason _ reached⟩
  · subst outcome
    obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.initializer_fault mono measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _evaluated, represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      cases represented with
      | value payload =>
        have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
        have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        obtain ⟨_captured, _captures, _capturedTyped, _allocationEval, nextEnvironments, nextHeaps, nextLocals,
            nextAgrees, nextTyped, nextReference, nextRead, allocationFrame, nextState, _allocatedRelated, nextAdmitted⟩ :=
          CallableIndexedOwnedAdmittedLexicalAllocation.allocate_initialized bridge functions definitions registered producer
            mono extended ordinary allocation annotation same (sourceType ▸ post.at_value.1) (sourceType ▸ payload)
            (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
            reference frameRead allocated middleState ((acquire _ _ conditioned) middleState frameRead) post.at_value.2
        obtain ⟨_, _, resultHeap, restTrace, restAdapted⟩ := remaining
          (Nat.le_trans (Nat.le_of_lt tailStrict) within)
          ⟨_, _, _, nextEnvironments, nextHeaps, nextLocals, nextAgrees, nextTyped,
            nextReference, nextRead, (allocationFrame contextLocation stillUnmapped (List.getElem?_eq_some_iff.mp frameRead).1).1,
            nextState, conditioned, nextAdmitted⟩ tail
        exact ⟨_, _, resultHeap,
          CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_initialized mono extended measured allocated restTrace,
          restore_adapted environment restAdapted⟩

variable {administrative : Core.Context}

include bridge functions condition in
/-- A completed expression supplies the real next physical state before the
suffix is lifted. A rejected expression stops at its own reached heap. -/
theorem discard {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition rest test postItems statements budget) :
    InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition (.expression expression :: rest) test postItems statements budget := by
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  rcases SelectedCompilationStageForInitialInversion.discard trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, strict, tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.expression_fault measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, middleState, _related, post⟩ :=
        preservation stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted measured
      have frameRead := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
      have stillUnmapped := (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      obtain ⟨_, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata, agrees,
          actualTyped.weaken worlds, reference, frameRead, stillUnmapped, middleState, conditioned, post.at_value.2⟩ tail
      exact ⟨_, result, finalHeap, CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_expression measured restTrace, restAdapted⟩

variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)

include bridge functions condition transport extension in
/-- Value assignment lifts the RHS at the original target snapshot. The
existing real write producer supplies the next physical state for the suffix. -/
theorem assign {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {rest postItems : List ForItemForm} {test : ExpressionId} {statements : List StatementId}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
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
  obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative)
    functions extension head bare environments heaps locals agrees
  rcases SelectedCompilationStageForInitialInversion.assign snapshot trace with
    ⟨childSize, reason, strict, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, strict, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, strict, tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_operands snapshot measured
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      exact ⟨_, _, _, CallableIndexedOwnedAdmittedStagedForInitializerSource.assignment_fault snapshot measured,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.preserves_value
          (compiled := compiled) (values := .initial compiled.compatible.checked)
          (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
          (context := context) (scope := scope) (administrative := administrative)
          bridge functions extension transport head bare environments heaps locals agrees actualTyped initial admitted unique assignmentTyped
          (preservation stagedSize) snapshot measured write
      obtain ⟨_, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (Nat.le_trans (Nat.le_of_lt tailStrict) within)
        ⟨_, _, _, environments.extend maps worlds, middleHeaps,
          locals.mono metadata, DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, reference,
          ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
          (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1,
          middleState, conditioned, nextAdmitted⟩ tail
      exact ⟨_, result, finalHeap,
        CallableIndexedOwnedAdmittedStagedForInitializerSource.prepend_assignment snapshot measured write restTrace, restAdapted⟩

variable {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations compiled.compatible.checked.catalog functions identities)
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (diagnostics : PreparedAssignmentReachedDiagnostics.Ready (values := .initial compiled.compatible.checked) functions callerProtocol invocation.source
    invalidProjection missingDefault receiving (fun reason token => faults (.semantic reason) token))

include definitions registered transport extension faithful observations diagnostics in
/-- Empty initialization enters the same finite loop. Its post-header lifting
is built from the actual compiler tree, including all original allocations. -/
theorem done {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (bindings : ProtectedStateTransition.Bindings callerProtocol)
    (marked : ProtectedStateTransition.MarkedAllocation.Producer callerProtocol layouts frame model)
    (markedAcquire : ∀ location native, condition location native →
      ProtectedStateTransition.OrdinaryAllocation.ReadyAt marked.toOrdinary location native)
    (children : ∀ context childSize, childSize < budget →
      LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation (certificates context) faults childSize)
    (unique : NodeOccurrencesUnique invocation.source)
    {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {postItems : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {control : ControlContext}
    (found : invocation.source.lookupExpression? test = some node)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificates context scope test ⟨.bool, testCode⟩)
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (bodyPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowPreserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode n)
    (postTree : GenericForHeader.Tree layouts owner active frame globals onError (.initial compiled.compatible.checked)
      invocation.source (CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate invocation.source certificates)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions administrative
      type (TypedForHeader.Fallthrough type) context scope postItems postCode)
    {catalogFaults : FunctionCalls.FaultRep}
    (postErrors : PreparedBranchingCatalogSites.HeaderSites invalidProjection missingDefault receiving catalogFaults postTree)
    (semantic : ∀ reason token, catalogFaults reason token → faults (.semantic reason) token)
    (postShape : CallableIndexedOwnedPreparedStagedBranchingTree.ItemShape postItems)
    (postTyped : CallableIndexedOwnedPreparedStagedForItemsTyping.Facts invocation.source control context postItems) :
    InitializersLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (context := context) (scope := scope)
      bridge functions condition [] test postItems statements budget := by
  have postLift : ItemsLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (context := context) (scope := scope)
      bridge functions condition postItems budget :=
    SelectedCompilationStageForHeaderLifting.lifts bridge functions faithful observations definitions registered marked.toOrdinary
      condition markedAcquire transport extension children preservation unique postTree postShape postTyped
  have postPreservation (n : Nat) : CallableIndexedOwnedAdmittedStagedForPostContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope postItems expected type postCode n := by
    exact CallableIndexedOwnedAdmittedStagedForHeaderPreservation.preserves_at bridge bindings transport functions faithful observations extension
      definitions registered marked condition markedAcquire diagnostics (fun c m _ => preservation c m) unique postTree postErrors semantic postShape postTyped
  intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
  cases trace with
  | initializerFault initial => cases initial
  | loop initial loop =>
    cases initial
    obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageForLifting.for_ready
      bridge functions condition (children context) (preservation context) found typed generated body bodyPreservation
      postLift postPreservation (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
      ready loop
    obtain ⟨grade, measured⟩ := Staging.Recursive.Size.ForLoop.of_trace lifted
    exact ⟨_, _, _, .loop .empty measured, restore_adapted environment adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
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

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

open SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open SelectedCompilationStageForInitialBounds (InitializersLifts)

def PositionLifts {administrative : Core.Context} (context : SourceSemantics.Context)
    (scope : SourceCoreLocalCell.Scope) (position : GenericImperativeMatch.Position) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget
  | .initializers items test post statements => InitializersLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      (context := context) (scope := scope) bridge functions condition items test post statements budget

include bridge bindings definitions registered producer acquire transport extension faithful observations in
theorem preserves_position
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
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
    ∀ budget, CallableIndexedOwnedAdmittedStagedImperativePositions.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope position expected type code budget := by
  intro budget
  exact CallableIndexedOwnedAdmittedStagedScopedImperativePreservation.preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport
    functions faithful observations extension definitions registered producer condition acquire (fun context size _ => preservation context size)
    unique tree catalogSites shape sourceTyped projection

include bridge bindings definitions registered producer acquire transport extension faithful observations in
theorem lifts_position {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
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
    PositionLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope position budget := by
  have typedChildren (context : SourceSemantics.Context) (size : Nat) (smaller : size < budget) :
      LiftsAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) size := by
    intro scope id lowered generated node found typed
    obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
    exact children context size smaller certified found typed
  have typedPreservation (context : SourceSemantics.Context) (size : Nat) :
      PreservesAt bridge context model stages invocation (TypedCertificate invocation.source certificates context) faults size := by
    intro scope id lowered generated node found typed
    obtain ⟨actualNode, nodeFound, nodeTyped, certified⟩ := generated
    exact preservation context size certified found typed
  revert shape sourceTyped projection
  induction catalogSites with
  | @body context scope mode statements expected type code syntaxTree body =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    exact SelectedCompilationStageLexicalTreeLifting.lifts bridge bindings functions definitions registered producer.toOrdinary
      condition acquire children preservation unique body shape projection within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @uninitialized context nextContext scope mode id node binder rest expected type body payload found form mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    exact SelectedCompilationStageLexicalLifting.absent bridge functions definitions registered producer.toOrdinary condition acquire
      unique found form mono extended ordinary projected allocation annotation same
      (ih (shape.tail_of_let found form) (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @initialized context nextContext scope mode id node binder initializer initializerNode lowered body rest expected type found form mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (initialFound.symm.trans typedFound)
    exact SelectedCompilationStageLexicalLifting.initialized bridge functions definitions registered producer.toOrdinary condition acquire
      unique found form mono extended ordinary initialFound sourceType typed certified allocation annotation same
      (children _) (preservation _)
      (ih (shape.tail_of_let found form) (ProtectedStateImperativeStatementSuffixTyping.let_decl unique sourceTyped found form extended) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @discard context scope mode id node expression expressionNode semi rest expected lowered type body found form guard expressionFound child remaining remainingErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨continuing, tailShape⟩ := shape.discard_tail found form guard
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (expressionFound.symm.trans typedFound)
    exact SelectedCompilationStageDiscardLifting.lifts bridge functions condition unique found form continuing expressionFound typed certified
      (children _) (preservation _) (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.discard unique sourceTyped found form) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @assign context scope mode id node assignment operator rhs rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨_profile, tailShape⟩ := shape.assignment_tail found form
    have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    by_cases bare : assignment.target.projections = []
    · exact SelectedCompilationStageAssignmentLifting.lifts bridge functions transport extension condition unique found form head bare assignmentTyped
        (typedChildren context) (typedPreservation context)
        (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
    · exact SelectedCompilationStageProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension condition unique found form head bare assignmentTyped
        (typedChildren context) (typedPreservation context)
        (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.assignment unique sourceTyped found form) projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @block context scope mode id node statements rest expected type innerCode body found form inner remaining innerErrors remainingErrors innerIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨innerShape, restShape⟩ := shape.block_children found form
    have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
    have restTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (innerIH innerShape innerTyped projection)
      (preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
        preservation unique inner innerErrors innerShape innerTyped projection)
      (.inl (remainingIH restShape restTyped projection)) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @ifThen context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode body found form conditionFound conditionType conditionTree thenTree elseTree remaining thenTreeErrors elseTreeErrors remainingErrors thenIH elseIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨leftShape, rightShape, restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    refine SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then thenCode else elseCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _) ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
    · intro truth; cases truth
      · exact elseIH rightShape rightTyped projection
      · exact thenIH leftShape leftTyped projection
    · intro truth; cases truth
      · exact preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique elseTree elseTreeErrors rightShape rightTyped projection
      · exact preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique thenTree thenTreeErrors leftShape leftTyped projection
    · exact .inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping.suffix unique sourceTyped found form) projection)
  | @terminalBlock context scope mode id node statements rest expected type innerCode suffix exactUnique found form inner stops issued innerErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨innerShape, _restShape⟩ := shape.block_children found form
    have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner unique sourceTyped found form
    exact SelectedCompilationStageBlockLifting.lifts bridge functions condition unique found form
      (ih innerShape innerTyped projection)
      (preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique inner innerErrors innerShape innerTyped projection)
      (.inr stops) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalIf context scope mode id node conditionId conditionNode thenBody elseBody rest expected type conditionCode thenCode elseCode suffix exactUnique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued thenErrors elseErrors thenIH elseIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨leftShape, rightShape, _restShape⟩ := shape.branches found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have leftTyped := ProtectedStateImperativeTypedSourceSites.branch_typed true unique (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    have rightTyped := ProtectedStateImperativeTypedSourceSites.branch_typed false unique (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    refine SelectedCompilationStageConditionalLifting.lifts (expected := expected) (type := type)
      (branchCode := fun truth => if truth then thenCode else elseCode) bridge functions condition unique found form
      conditionFound typed certified (children _) (preservation _) ?_ ?_ ?_ within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
    · intro truth; cases truth
      · exact elseIH rightShape rightTyped projection
      · exact thenIH leftShape leftTyped projection
    · intro truth; cases truth
      · exact preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique elseTree elseErrors rightShape rightTyped projection
      · exact preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique thenTree thenErrors leftShape leftTyped projection
    · exact .inr ⟨thenStops, elseStops⟩
  | @whileLoop context scope mode id node conditionId conditionNode statements rest expected type conditionCode loopCode body selfReason found form conditionFound conditionType conditionTree loopTree nativeTyped remaining loopBodyErrors remainingErrors loopIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨loopShape, restShape⟩ := shape.loop found form
    obtain ⟨typedNode, typedFound, typed, certified⟩ := conditionTree
    cases Option.some.inj (conditionFound.symm.trans typedFound)
    have loopTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children unique sourceTyped found form).2
    have restTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageWhileSequenceLifting.lifts bridge functions condition transport
      (children _) (preservation _) conditionFound conditionType typed certified nativeTyped
      (loopIH loopShape loopTyped projection)
      (preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire preservation unique loopTree loopBodyErrors loopShape loopTyped projection)
      unique found form (remainingIH restShape restTyped projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @matchWith context scope mode id node resolution scrutineeNode rest expected type matched body selfReason control caseFacts found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren remaining catalog patternContext childErrors remainingErrors matchIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    cases compilation with
    | mk values solved sourceCells ambientDefinitions =>
      cases sameValues
      have selectedMeaning : SelectedCompilationStageMatchSequences.MatchLifts
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation)
          bridge functions condition context scope resolution budget :=
        SelectedCompilationStageMatchTreeHeads.lifts bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped budget condition producer bindings acquire unique
          (typedChildren context) (typedPreservation context)
          (fun request member childContext selectedContext bodyTyped =>
            matchIH request member childContext selectedContext (shape.match_request found form selectedContext.forget) bodyTyped projection)
      have selectedPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope resolution expected type matched n := by
        intro n matchSize
        exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
          bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
          n condition producer bindings acquire unique (fun childSize _ => typedPreservation context childSize)
          (fun request member childContext selectedContext bodyTyped =>
            preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
              preservation unique (matchChildren request member childContext selectedContext)
              (childErrors request member childContext selectedContext)
              (shape.match_request found form selectedContext.forget) bodyTyped projection n)
      obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
      exact SelectedCompilationStageMatchSequences.lifts bridge functions condition unique found form selectedMeaning selectedPreservation
        (.inl (remainingIH restShape (CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping.suffix unique sourceTyped found form) projection)) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @terminalMatch context scope mode id node resolution scrutineeNode rest expected type matched suffix selfReason control caseFacts exactUnique found form scrutineeFound scrutineeTyped casesTyped defaultTyped compilation sameValues sameDefinitions allocator requests receipt ordinary matchChildren stops issued catalog patternContext childErrors matchIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    cases compilation with
    | mk values solved sourceCells ambientDefinitions =>
      cases sameValues
      have selectedMeaning : SelectedCompilationStageMatchSequences.MatchLifts
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation)
          bridge functions condition context scope resolution budget :=
        SelectedCompilationStageMatchTreeHeads.lifts bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped budget condition producer bindings acquire unique
          (typedChildren context) (typedPreservation context)
          (fun request member childContext selectedContext bodyTyped =>
            matchIH request member childContext selectedContext (shape.match_request found form selectedContext.forget) bodyTyped projection)
      have selectedPreservation : ∀ n, CallableIndexedOwnedAdmittedStagedMatchSequences.MatchPreserves
          (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
          (stages := stages) (invocation := invocation) (faults := faults)
          bridge functions condition context scope resolution expected type matched n := by
        intro n matchSize
        exact CallableIndexedOwnedAdmittedStagedMatchTreeHeads.preserves (size := matchSize)
          bridge functions onError allocator definitions registered extension receipt ordinary
          patternContext.signatures catalog scrutineeFound scrutineeTyped casesTyped defaultTyped
          n condition producer bindings acquire unique (fun childSize _ => typedPreservation context childSize)
          (fun request member childContext selectedContext bodyTyped =>
            preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
              preservation unique (matchChildren request member childContext selectedContext)
              (childErrors request member childContext selectedContext)
              (shape.match_request found form selectedContext.forget) bodyTyped projection n)
      obtain ⟨_armShapes, _defaultShape, restShape⟩ := shape.match_children found form
      exact SelectedCompilationStageMatchSequences.lifts bridge functions condition unique found form selectedMeaning selectedPreservation
        (.inr stops) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @breaking context scope mode id node rest expected type found form =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
        environment before (id :: rest) finalContext outcome after := by
      cases mode <;> exact trace.sound
    obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.breaking_view unique found form ordinary
    exact ⟨_, _, _, .breaking (lookupStatement?_sound found) form, .completed (.breaking environment)⟩
  | @continuing context scope mode id node rest expected type found form =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
        environment before (id :: rest) finalContext outcome after := by
      cases mode <;> exact trace.sound
    obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.continuing_view unique found form ordinary
    exact ⟨_, _, _, .continuing (lookupStatement?_sound found) form, .completed (.continuing environment)⟩
  | @bitNot context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨_rawWord, _bare, tailShape⟩ := shape.bitNot_tail found form head.bare
    have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    exact SelectedCompilationStageBitNotLifting.lifts bridge functions transport condition unique found form head assignmentTyped
      (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.bitNot unique sourceTyped found form) projection)
      within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @bitNotProjected context scope mode id node assignment rest expected type body found form head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨_rawWord, tailShape⟩ := shape.unary_tail found form
    have assignmentTyped := ProtectedStateImperativeTypedSourceSites.bit_not unique
      (ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
    exact SelectedCompilationStageProjectedBitNotLifting.lifts bridge functions faithful observations transport extension condition unique found form head head.projected assignmentTyped
      (typedChildren context) (typedPreservation context)
      (ih tailShape (ProtectedStateImperativeStatementSuffixTyping.bitNot unique sourceTyped found form) projection)
      within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @forLoop context scope mode id node items test post statements rest expected type initialCode body found form initialTree remaining initialErrors remainingErrors initialIH remainingIH =>
    intro shape sourceTyped projection size within mapping world actualContext environment canonical actual before store ξ
      contextLocation native environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted
      finalContext outcome after trace
    obtain ⟨initialShape, postShape, loopShape, restShape⟩ := shape.for_children found form
    have initialTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.children unique sourceTyped found form
    have tailTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix unique sourceTyped found form
    exact SelectedCompilationStageForSequenceLifting.lifts bridge functions condition
      (initialIH ⟨initialShape, postShape, loopShape⟩ initialTyped projection)
      (preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
        preservation unique initialTree initialErrors ⟨initialShape, postShape, loopShape⟩ initialTyped projection)
      unique found form (remainingIH restShape tailTyped projection) within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace
  | @initializersDone context scope test node post statements expected type testCode bodyCode postCode selfReason found nodeType certified bodyTree postTree nativeTyped bodyErrors postErrors bodyIH =>
    intro shape sourceTyped projection
    obtain ⟨control, _testTyped, bodyTyped, postTyped⟩ := InitializerTyping.nil sourceTyped
    obtain ⟨typedNode, typedFound, typed, generated⟩ := certified
    cases Option.some.inj (found.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.done bridge functions definitions registered condition transport extension faithful observations assignmentDiagnostics
      bindings producer acquire children preservation unique found typed generated
      (bodyIH shape.2.2 bodyTyped projection)
      (preserves_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
        preservation unique bodyTree bodyErrors shape.2.2 bodyTyped projection)
      postTree postErrors semantic shape.2.1 postTyped within ready trace
  | @initializerUninitialized context nextContext scope binder rest body payload test post statements expected type mono extended ordinary projected allocation annotation same tail remainingErrors ih =>
    intro shape sourceTyped projection
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.absent bridge functions definitions registered producer.toOrdinary condition acquire
      mono extended ordinary projected allocation annotation same
      (ih ⟨shape.1.let_tail, shape.2⟩ (InitializerTyping.absent sourceTyped extended) projection) within ready trace
  | @initializerInitialized context nextContext scope binder initializer initializerNode lowered body rest test post statements expected type mono extended ordinary initialFound sourceType child allocation annotation same remaining remainingErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (initialFound.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.initialized bridge functions definitions registered producer.toOrdinary condition acquire
      mono extended ordinary initialFound sourceType typed certified allocation annotation same (children _) (preservation _)
      (ih ⟨shape.1.let_tail, shape.2⟩ (InitializerTyping.initialized sourceTyped mono extended) projection) within ready trace
  | @initializerDiscard context scope expression expressionNode rest lowered body test post statements expected type expressionFound child remaining remainingErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨typedNode, typedFound, typed, certified⟩ := child
    cases Option.some.inj (expressionFound.symm.trans typedFound)
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.discard bridge functions condition expressionFound typed certified
      (children _) (preservation _)
      (ih ⟨shape.1.discard_tail, shape.2⟩ (InitializerTyping.expression sourceTyped) projection) within ready trace
  | @initializerAssign context scope assignment operator rhs rest body test post statements expected type head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨_profile, tailShape⟩ := shape.1.assignment_tail
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    by_cases bare : assignment.target.projections = []
    · exact SelectedCompilationStageForInitialLifting.assign bridge functions condition transport extension unique head bare
        (InitializerTyping.assignment sourceTyped).1 (typedChildren context) (typedPreservation context)
        (ih ⟨tailShape, shape.2⟩ (InitializerTyping.assignment sourceTyped).2 projection) within ready trace
    · exact SelectedCompilationStageForInitialLifting.assignProjected bridge functions faithful observations transport extension condition unique head bare
        (InitializerTyping.assignment sourceTyped).1 (typedChildren context) (typedPreservation context)
        (ih ⟨tailShape, shape.2⟩ (InitializerTyping.assignment sourceTyped).2 projection) within ready trace
  | @initializerBitNot context scope assignment rest body test post statements expected type head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨_rawWord, _bare, tailShape⟩ := shape.1.bitNot_tail head.bare
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.bitNot bridge functions transport condition head
      (InitializerTyping.bitNot sourceTyped).1
      (ih ⟨tailShape, shape.2⟩ (InitializerTyping.bitNot sourceTyped).2 projection) within ready trace
  | @initializerBitNotProjected context scope assignment rest body test post statements expected type head remaining remainingErrors headErrors ih =>
    intro shape sourceTyped projection
    obtain ⟨_rawWord, tailShape⟩ := shape.1.unary_tail
    intro size within environment canonical actual actualContext ξ contextLocation native before after ready outcome trace
    exact SelectedCompilationStageForInitialLifting.bitNotProjected bridge functions faithful observations transport extension condition unique head head.projected
      (InitializerTyping.bitNot sourceTyped).1 (typedChildren context) (typedPreservation context)
      (ih ⟨tailShape, shape.2⟩ (InitializerTyping.bitNot sourceTyped).2 projection) within ready trace

include bridge bindings definitions registered producer acquire transport extension faithful observations in
theorem lifts_at {budget : Nat}
    (children : ∀ context childSize, childSize < budget → LiftsAt bridge context model stages invocation (certificates context) childSize)
    (preservation : ∀ context size, PreservesAt bridge context model stages invocation (certificates context) faults size)
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
    (projection : compiled.compatible.checked.catalog.project expected = .ok type) :
    FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope mode statements budget := by
  cases atStatements
  exact lifts_position (semantic := semantic) (assignmentDiagnostics := assignmentDiagnostics) bridge bindings transport functions faithful observations extension definitions registered producer condition acquire
    children preservation unique tree catalogSites shape sourceTyped projection

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageImperativeLifting
end
