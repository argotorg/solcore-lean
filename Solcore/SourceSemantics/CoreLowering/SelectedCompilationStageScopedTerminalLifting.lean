import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
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
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


include bridge functions condition in
theorem nil {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode [] budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨_, .fallthrough environment, _, .nil, .completed (.fallthrough environment)⟩

include bridge functions condition in
theorem return_unit {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode (id :: rest) budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit unique found form trace
  exact ⟨_, .returned .unit, _, .returnUnit (lookupStatement?_sound found) form,
    .completed (.returned .unit)⟩

include bridge functions condition in
theorem terminal {budget : Nat} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expression : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {certificate : GenericExpressionMeaning.Certificate}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : CallableIndexedOwnedAdmittedStagedScopedTerminalStatements.Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (typed : ExpressionHasType invocation.source context expression node.type)
    (generated : certificate scope expression lowered)
    (children : ∀ childSize, childSize < budget → LiftsAt bridge context model stages invocation certificate childSize) :
    FlowLifts (administrative := administrative) (receiving := receiving)
      (frame := frame) (globals := globals) (stages := stages) (invocation := invocation)
      bridge functions condition context scope mode statements budget := by
  intro size within mapping world actualContext environment canonical actual before store ξ
    contextLocation native environments heaps locals agrees actualTyped reference read unmapped
    initial conditioned admitted finalContext outcome after trace
  obtain ⟨childSize, plain, strict, rfl, rfl, evaluated⟩ :=
    SelectedCompilationStageScopedTerminalInversion.child_of_body unique head trace
  have lifted := children childSize (Nat.lt_of_lt_of_le strict within) generated found typed
    environments heaps locals agrees actualTyped initial admitted evaluated
  obtain ⟨stagedSize, staged, reached, stagedTrace, adapted⟩ := lifted.sized
  refine ⟨_, _, reached, (head.trace stagedTrace).sound, ?_⟩
  cases adapted with
  | completed => cases plain with
    | value value => exact .completed (.returned value)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason reached => exact .rejected origin call reason _ reached

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalLifting
