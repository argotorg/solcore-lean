import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareAssignmentHeads

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
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
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
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
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CallableIndexedOwnedAdmittedStagedBareAssignmentHeads.target_snapshot
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) (invocation := invocation)
    (context := context) (scope := scope) (administrative := administrative)
    functions extension head bare environments heaps locals agrees
  rcases SelectedCompilationStageAssignmentInversion.child_and_tail unique found form snapshot trace with
    ⟨childSize, reason, strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, strict, tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareOperands (lookupStatement?_sound found) form snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children childSize (Nat.lt_of_lt_of_le strict within) head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
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
        (Nat.le_trans (Nat.le_of_lt tailStrict) within) (environments.extend maps worlds) middleHeaps
        (locals.mono metadata) (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped reference
        ((framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read)
        (framePreserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1
        middleState conditioned nextAdmitted tail
      exact ⟨nextContext, result, finalHeap,
        .assignBare (lookupStatement?_sound found) form snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentLifting
