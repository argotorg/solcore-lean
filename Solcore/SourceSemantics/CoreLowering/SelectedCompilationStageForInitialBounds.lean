import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageWhileLifting
open SelectedCompilationStageForLiftBounds
universe u

inductive PlainInitial (program : Program) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) :
    Nat → Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | initializerFault {size finalContext reason after}
      (trace : SourceExecutionSize.ForItemsFault program size context invocation.evidence invocation.source
        environment before items finalContext reason after) :
      PlainInitial program invocation context environment before items test post statements
        (SourceExecutionSize.stepSize [size]) (.fault reason) after
  | loop {initialSize loopSize loopContext loopEnvironment middle outcome after}
      (initial : SourceExecutionSize.ForItemsExecute program initialSize context invocation.evidence invocation.source
        environment before items loopContext loopEnvironment middle)
      (trace : PlainFor program loopSize invocation loopContext loopEnvironment middle test post statements outcome after) :
      PlainInitial program invocation context environment before items test post statements
        (SourceExecutionSize.stepSize [initialSize, loopSize]) (Dynamic.restoreControl environment outcome) after

def InitialLift (program : Program) (stages : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (outcome : Dynamic.ControlOutcome) (after : Dynamic.Heap) : Prop :=
  ∃ size staged reached,
    CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace program stages invocation context environment before
      items test post statements size staged reached ∧
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

def InitializersLifts (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm)
    (statements : List StatementId) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
    {ξ : Renaming} {contextLocation : Location} {native : NativeFrame} {before after : Dynamic.Heap},
    PhysicalReady (administrative := administrative) (receiving := receiving) (frame := frame)
      (globals := globals) (context := context) (scope := scope)
      bridge functions condition environment canonical actual actualContext ξ contextLocation native before →
    ∀ {outcome : Dynamic.ControlOutcome},
      PlainInitial program invocation context environment before items test post statements size outcome after →
      InitialLift program stages invocation context environment before items test post statements outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialBounds
