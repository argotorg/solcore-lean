import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileLifting

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageScopedLiftBounds SelectedCompilationStageBodyLiftBounds
open CallableIndexedOwnedAdmittedStagedConditionalHeads
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}

local notation "ReadyAt" => SelectedCompilationStageWhileLifting.PhysicalReady (administrative := administrative) (receiving := receiving)
  (frame := frame) (globals := globals) (context := context) (scope := scope)
  bridge functions condition environment canonical actual actualContext ξ contextLocation native

theorem body_prefix {budget size : Nat} {before after : Dynamic.Heap}
    {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
    (body : FlowLifts (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) bridge functions condition context scope false statements budget)
    (ready : ReadyAt before) (within : size ≤ budget)
    (trace : RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence invocation.source
      environment before statements finalContext outcome after) :
    BodyLift program stages false invocation context environment before statements finalContext outcome after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  exact body within environments heaps locals agrees actualTyped reference read unmapped initial conditioned admitted trace

theorem body_ready {before after : Dynamic.Heap} {finalContext : SourceSemantics.Context}
    {finalEnvironment : Dynamic.Environment}
    (preservation : ∀ budget, FlowPreserves (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope false statements expected type loopCode budget)
    (ready : ReadyAt before)
    (trace : Staging.Recursive.StatementsIn program stages false invocation context environment before statements
      finalContext (.fallthrough finalEnvironment) after) : ReadyAt after := by
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, reference, read, unmapped,
    initial, conditioned, admitted⟩ := ready
  obtain ⟨size, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace trace
  obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata,
    last, _, post⟩ := preservation size (Nat.le_refl _) environments heaps locals agrees actualTyped
      reference read unmapped initial conditioned admitted measured
  exact ⟨finalMap, finalWorld, finalStore, environments.extend maps worlds, finalHeaps, locals.mono metadata,
    agrees, actualTyped.weaken worlds, reference,
    ((preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read),
    (preserved contextLocation unmapped (List.getElem?_eq_some_iff.mp read).1).1, last, conditioned, post⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
