import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding

/-! The same compiler tree contains statement sequences and for initializer
prefixes. Each position carries its original Source typing and its own trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
universe u

def InitializerTyping (source : TypedSource) (context : SourceSemantics.Context)
    (items : List ForItemForm) (test : ExpressionId) (post : List ForItemForm) (statements : List StatementId) : Prop :=
  ∃ control loopContext postContext bodyFinal bodyFacts,
    ForItemsHaveType source control context items loopContext ∧
    ExpressionHasType source loopContext test .bool ∧
    StatementsHaveType source control.enterLoop loopContext statements bodyFinal bodyFacts ∧
    ForItemsHaveType source control.enterLoop loopContext post postContext

def PositionTyping (source : TypedSource) (context : SourceSemantics.Context) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => ProtectedStateImperativeTypedSourceSites.Statements source context statements
  | .initializers items test post statements => InitializerTyping source context items test post statements

namespace InitializerTyping
variable {source : TypedSource} {context nextContext : SourceSemantics.Context}
  {test : ExpressionId} {post : List ForItemForm} {statements : List StatementId} {rest : List ForItemForm}

theorem nil (typed : InitializerTyping source context [] test post statements) :
    ∃ control, ExpressionHasType source context test .bool ∧
      ProtectedStateImperativeTypedSourceSites.Statements source context statements ∧
      CallableIndexedOwnedPreparedStagedForItemsTyping.Facts source control context post := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial
  exact ⟨control.enterLoop, condition, ⟨control.enterLoop, bodyFinal, bodyFacts, body⟩, postContext, post⟩

theorem absent {binder : TypedBinder}
    (typed : InitializerTyping source context (.letDecl binder none :: rest) test post statements)
    (extended : BinderExtends source.owner context binder nextContext) :
    InitializerTyping source nextContext rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | letUninitialized _ _ actual =>
      cases Dynamic.BinderExtends.functional extended actual
      exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩

theorem initialized {binder : TypedBinder} {expression : ExpressionId}
    (typed : InitializerTyping source context (.letDecl binder (some expression) :: rest) test post statements)
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends source.owner context binder nextContext) :
    InitializerTyping source nextContext rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | letInitialized _ _ _ actual =>
      cases Dynamic.BinderExtends.functional extended actual
      exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩
    | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim

theorem expression {expression : ExpressionId}
    (typed : InitializerTyping source context (.expression expression :: rest) test post statements) :
    InitializerTyping source context rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head
    exact ⟨control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩

theorem assignment {assignment : AssignmentResolution} {operator : Solcore.Syntax.ValueAssignOp} {rhs : ExpressionId}
    (typed : InitializerTyping source context (.assignValue assignment operator rhs :: rest) test post statements) :
    SourceAssignmentHasType source context assignment operator rhs ∧
    InitializerTyping source context rest test post statements := by
  obtain ⟨control, loopContext, postContext, bodyFinal, bodyFacts, initial, condition, body, post⟩ := typed
  cases initial with
  | cons head tail =>
    cases head with
    | assignValue actual => exact ⟨actual, control, loopContext, postContext, bodyFinal, bodyFacts, tail, condition, body, post⟩
end InitializerTyping

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

theorem represents_restore {mapping world expected type outcome value environment}
    (related : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world false expected type faults outcome value) :
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Represents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      mapping world false expected type faults (outcome.restore environment) value := by
  cases related with
  | fallthrough _ allowed => exact .fallthrough _ allowed
  | returned payload => exact .returned payload
  | breaking _ => exact .breaking environment
  | continuing _ => exact .continuing environment
  | fault matched => exact .fault matched

theorem post_restore {context expected outcome environment index} {reached : callerProtocol.State index}
    (post : CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post bridge context expected outcome reached) :
    CallableIndexedOwnedAdmittedStagedFlowOutcomes.Post bridge context expected (outcome.restore environment) reached := by
  cases outcome <;> exact post

def Reflects (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowReflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode statements expected type code budget
  | .initializers items test post statements => CallableIndexedOwnedAdmittedStagedForHeadContracts.Reflects
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type code budget

def Preserves (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (position : GenericImperativeMatch.Position) (expected : TypeSystem.Ty) (type : Ty) (code : Expr) (budget : Nat) : Prop :=
  match position with
  | .statements mode statements => CallableIndexedOwnedAdmittedStagedConditionalHeads.FlowPreserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope mode statements expected type code budget
  | .initializers items test post statements => CallableIndexedOwnedAdmittedStagedForHeadContracts.Preserves
      (administrative := administrative) (receiving := receiving) (frame := frame) (globals := globals)
      (stages := stages) (invocation := invocation) (faults := faults)
      bridge functions condition context scope items test post statements expected type code budget

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedImperativePositions
