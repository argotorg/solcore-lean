import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBitNotInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedBareBitNotHeads

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
