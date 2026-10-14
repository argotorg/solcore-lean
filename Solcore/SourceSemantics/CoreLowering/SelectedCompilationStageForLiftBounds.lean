import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePhysicalReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeads

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds SelectedCompilationStageScopedLiftBounds
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
universe u

inductive PlainItems (program : Program) (size : Nat) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) : SourceSemantics.Context → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | done {finalContext finalEnvironment after}
      (trace : SourceExecutionSize.ForItemsExecute program size context invocation.evidence invocation.source
        environment before items finalContext finalEnvironment after) :
      PlainItems program size invocation context environment before items finalContext (.fallthrough finalEnvironment) after
  | fault {finalContext reason after}
      (trace : SourceExecutionSize.ForItemsFault program size context invocation.evidence invocation.source
        environment before items finalContext reason after) :
      PlainItems program size invocation context environment before items finalContext (.fault reason) after

def itemsControl : Staging.Recursive.ForItemsOutcome → Staging.Recursive.BodyOutcome
  | .done environment => .fallthrough environment
  | .fault reason => .fault reason

def ItemsLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (finalContext : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ stagedContext staged reached,
    Staging.Recursive.ForItems program stages invocation context environment before items stagedContext staged reached ∧
    BodyAdapted finalContext outcome after stagedContext (itemsControl staged) reached

inductive PlainFor (program : Program) (size : Nat) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | control {outcome after}
      (trace : SourceExecutionSize.ForLoopExecutes program size context invocation.evidence invocation.source
        environment before test post statements context outcome after) :
      PlainFor program size invocation context environment before test post statements outcome after
  | fault {reason after}
      (trace : SourceExecutionSize.ForLoopFaults program size context invocation.evidence invocation.source
        environment before test post statements reason after) :
      PlainFor program size invocation context environment before test post statements (.fault reason) after

def ForLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Staging.Recursive.ForLoop program stages invocation context environment before test post statements staged reached ∧
    BodyAdapted context outcome after context staged reached

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
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {post : List ForItemForm}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode : Expr}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

def ItemsLifts (items : List ForItemForm) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {before after : Dynamic.Heap},
    PhysicalReady (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before →
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      PlainItems program size invocation context environment before items finalContext outcome after →
      ItemsLift program stages invocation context environment before items finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
