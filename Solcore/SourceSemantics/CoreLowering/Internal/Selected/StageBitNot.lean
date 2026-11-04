import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageExpressions
import Solcore.SourceSemantics.Staging.RecursiveBareBitNotFacts
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageForLoops
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.StageAssignments

/-!
# Lifting to staged Source: bit-not updates

Inversion and lifting of bare and projected bit-not updates, and of projected bit-not `for` initializers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds
open Staging.Recursive (BareTarget)

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
  {size : Nat} {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

private theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment
      before id finalContext outcome after) :
    ∃ target updated, finalContext = context ∧ outcome = .fallthrough environment ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  rename_i executed
  obtain ⟨target, snapshot, written⟩ := Staging.Recursive.bitNot_update_iff bare |>.mp executed.sound
  exact ⟨target, snapshot, _, written⟩

private theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment
      before id reason after) :
    after = before ∧ Dynamic.SourcePlaceBitNotFaults program context evidence source environment
      before assignment.target reason before := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  rename_i failed
  exact Staging.Recursive.bitNot_fault_iff bare |>.mp failed.sound

/-- The ordinary bare unary head either fails without changing its incoming
heap, or writes and reaches its strictly smaller suffix. -/
theorem write_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ reason, finalContext = context ∧ outcome = .fault reason ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source environment
        before assignment.target reason before) ∨
    (∃ tailSize target updated written, tailSize < size ∧
      BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, _strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, _strict, tailStrict, head, tail⟩
  · obtain ⟨sameHeap, failed⟩ := statement_fault unique found form bare failed
    exact .inl ⟨reason, equalContext, equalOutcome, sameHeap, failed⟩
  · obtain ⟨target, updated, equalContext, equalOutcome, snapshot, written⟩ :=
      statement_value unique found form bare head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨SourceExecutionSize.stepSize [], target, updated, after, ?_, snapshot, written, ?_⟩
      · have positive := head.positive
        simp only [SourceExecutionSize.stepSize, List.sum_nil]
        omega
      · cases mode <;> exact .control .nil
  · obtain ⟨target, updated, equalContext, equalOutcome, snapshot, written⟩ :=
      statement_value unique found form bare head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨tailSize, target, updated, middle, tailStrict, snapshot, written, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
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
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleBitNotStatements.Head context scope assignment)
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  rcases SelectedCompilationStageBitNotInversion.write_and_tail unique found form head.bare trace with
    ⟨reason, rfl, rfl, rfl, failed⟩ |
    ⟨tailSize, target, updated, written, tailStrict, snapshot, write, tail⟩
  · exact ⟨_, _, _, .bitNotBareFault (lookupStatement?_sound found) form head.bare failed,
      .completed (.fault reason)⟩
  · obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
        _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
      CallableIndexedOwnedAdmittedStagedBareBitNotHeads.preserves_value
        (compiled := compiled) (values := .initial compiled.compatible.checked)
        (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
        (context := context) (scope := scope) (administrative := administrative)
        bridge functions transport head environments heaps locals agrees actualTyped initial admitted assignmentTyped
        snapshot write
    obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
      (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
      (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped reference
      ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
      (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
      middleState conditioned nextAdmitted tail
    exact ⟨nextContext, result, finalHeap,
      .bitNotBare (lookupStatement?_sound found) form snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageForLiftBounds

variable {program : Program} {source : TypedSource}
  {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {id : StatementId} {node : StatementNode} {assignment : AssignmentResolution}
  {size : Nat}
  {outcome : Dynamic.ControlOutcome} {reason : Dynamic.SemanticFault}

theorem statement_value (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source environment before id finalContext outcome after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ outcome = .fallthrough environment ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context evidence source
        Dynamic.BitNotSnapshot environment before assignment.target updated after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, _, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem statement_fault (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source environment before id reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context evidence source environment
        before assignment.target reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars
  all_goals simp_all
  refine ⟨_, ?_, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

/-- Retain the genuine assignment derivation and independently measured suffix. -/
theorem child_and_tail {mode : Bool} {invocation : Staging.Recursive.Scope} {rest : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainStatements program mode tailSize invocation context environment written rest finalContext outcome after) := by
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨_, reason, strict, equalContext, equalOutcome, failed⟩ | ⟨_, strict, stopped, head⟩ |
    ⟨_, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, head, tail⟩
  · obtain ⟨assignedSize, childStrict, failed⟩ := statement_fault unique found form failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans childStrict strict, equalContext, equalOutcome, failed⟩
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst finalContext
    subst outcome
    rcases stopped with impossible | rfl
    · cases impossible
    · refine .inr ⟨assignedSize, SourceExecutionSize.stepSize [], updated, after,
        Nat.lt_trans childStrict strict, ?_, assigned, ?_⟩
      · simp only [SourceExecutionSize.stepSize, List.sum_nil]; omega
      · cases mode <;> exact .control .nil
  · obtain ⟨assignedSize, updated, childStrict, equalContext, equalOutcome, assigned⟩ :=
      statement_value unique found form head
    subst middleContext
    cases equalOutcome
    exact .inr ⟨assignedSize, tailSize, updated, middle,
      Nat.lt_trans childStrict strict, tailStrict, assigned, tail⟩

theorem item_value {nextEnvironment : Dynamic.Environment}
    (trace : SourceExecutionSize.ForItemExecutes program size context evidence source environment
      before (.assignBitNot assignment) finalContext nextEnvironment after) :
    ∃ assignedSize updated, assignedSize < size ∧ finalContext = context ∧ nextEnvironment = environment ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context evidence source
        Dynamic.BitNotSnapshot environment before assignment.target updated after := by
  cases trace with
  | assignBitNot assigned => exact ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, assigned⟩

theorem item_fault
    (trace : SourceExecutionSize.ForItemFaults program size context evidence source environment
      before (.assignBitNot assignment) reason after) :
    ∃ assignedSize, assignedSize < size ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context evidence source environment
        before assignment.target reason after := by
  cases trace with
  | assignBitNot failed => exact ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), failed⟩

theorem item_and_tail {invocation : Staging.Recursive.Scope} {rest : List ForItemForm}
    (trace : PlainItems program size invocation context environment before
      (.assignBitNot assignment :: rest) finalContext outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainItems program tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | done trace =>
      cases trace with
      | cons head tail =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .done tail⟩
  | fault trace =>
      cases trace with
      | head failed =>
          obtain ⟨assignedSize, strict, failed⟩ := item_fault failed
          exact .inl ⟨assignedSize, _, Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)), rfl, rfl, failed⟩
      | tail head failed =>
          obtain ⟨assignedSize, updated, strict, rfl, rfl, assigned⟩ := item_value head
          exact .inr ⟨assignedSize, _, updated, _,
            Nat.lt_trans strict (SourceExecutionSize.child_lt_stepSize (by simp)),
            SourceExecutionSize.child_lt_stepSize (by simp), assigned, .fault failed⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SourceCoreCompatibleDataPlaces DataPlaceExecution DataPatternValues
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
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
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (head : CompatibleProjectedBitNotStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment)
    (projected : assignment.target.projections ≠ [])
    (assignmentTyped : SourceBitNotAssignmentValid invocation.source context assignment)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation certificate faults childSize)
    (remaining : FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode rest budget) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
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
  rcases SelectedCompilationStageProjectedBitNotInversion.child_and_tail unique found form trace with
    ⟨assignedSize, reason, strict, rfl, rfl, failed⟩ |
    ⟨assignedSize, tailSize, updated, written, strict, tailStrict, assigned, tail⟩
  · cases failed with
    | target failed =>
      rcases SelectedCompilationStageProjectedTargetInversion.failed failed with
        ⟨rfl, rootFault⟩ | ⟨keySize, keyStrict, ready, keysFailed⟩ |
        ⟨keySize, values, keyStrict, ordinaryKeys, getterFault⟩
      · exact ⟨_, _, _, .bitNotProjectedRootFault (lookupStatement?_sound found) form projected rootFault, .completed (.fault reason)⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using keysFailed)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
      · obtain ⟨staged, reached, lifted, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge budget
          layout.children unique keyTyped children preservation environments heaps locals agrees actualTyped initial admitted
          (by simpa only [Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] using ordinaryKeys)
          (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega)
        have keys := lifted
        rw [← Staging.Recursive.ProjectedTarget.keys_eq_sourceKeys] at keys
        cases adapted with
        | completed =>
            exact ⟨_, _, _, .bitNotProjectedGetterFault (lookupStatement?_sound found) form projected keys getterFault, .completed (.fault reason)⟩
        | rejected origin call reason reached =>
            have ready : Staging.Recursive.ProjectedTarget.RootReady environment before assignment.target := by
              cases getterFault <;> exact .intro (by assumption) (by assumption)
            exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
    | uninitialized resolved empty =>
      rcases liftResolved resolved
        (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at *; omega) with
        ⟨origin, call, reason, reached, ready, keys⟩ |
        ⟨sources, keys, snapshot, keyValues, resolution, getterState, _getterRelated, getterAdmission⟩
      ·
        exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
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
        exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
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
      · exact ⟨_, _, _, .bitNotProjectedKeysFault (lookupStatement?_sound found) form projected ready keys, .rejected origin call reason _ reached⟩
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
          (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
          (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped reference
          ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
          (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
          middleState conditioned nextAdmitted tail
        exact ⟨nextContext, result, finalHeap,
          .bitNotProjected (lookupStatement?_sound found) form projected keys snapshot write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProjectedBitNotLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedBitNotInversion
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
open Frontend SourceInference
open SelectedCompilationStageForInitialBounds

/-- Preserve the actual assignment grade before the remaining initialization. -/
theorem bitNotProjected {program : Program} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {items post : List ForItemForm} {test : ExpressionId} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    {assignment : AssignmentResolution}
    (trace : PlainInitial program invocation context environment before
      (.assignBitNot assignment :: items) test post body size outcome after) :
    (∃ assignedSize reason, assignedSize < size ∧ outcome = .fault reason ∧
      SourceExecutionSize.SourcePlaceBitNotFaults program assignedSize context invocation.evidence invocation.source
        environment before assignment.target reason after) ∨
    (∃ assignedSize tailSize updated written, assignedSize < size ∧ tailSize < size ∧
      SourceExecutionSize.SourcePlaceSnapshotUpdate program assignedSize context invocation.evidence invocation.source
        Dynamic.BitNotSnapshot environment before assignment.target updated written ∧
      PlainInitial program invocation context environment written items test post body tailSize outcome after) := by
  rcases head trace with ⟨_, reason, strict, same, failed⟩ |
    ⟨_, _, _, _, _, _, childStrict, tailStrict, same, executed, tail⟩
  · obtain ⟨assignedSize, assignedStrict, failed⟩ := SelectedCompilationStageProjectedBitNotInversion.item_fault failed
    exact .inl ⟨assignedSize, reason, Nat.lt_trans assignedStrict strict, same, failed⟩
  · obtain ⟨assignedSize, updated, assignedStrict, rfl, rfl, assigned⟩ :=
      SelectedCompilationStageProjectedBitNotInversion.item_value executed
    rw [restored tail] at same
    subst outcome
    exact .inr ⟨assignedSize, _, updated, _, Nat.lt_trans assignedStrict childStrict, tailStrict, assigned, tail⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialProjectedBitNotLifting
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
end
