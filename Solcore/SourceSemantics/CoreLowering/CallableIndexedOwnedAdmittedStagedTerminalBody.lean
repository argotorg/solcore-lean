import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-! A terminal lexical body removes its original control envelope through the
existing toControl and finish helpers. Actual native prefix inversion supplies
the strict return-helper child; staged expression reflection reconstructs the
Source body at the same endpoint. No completed statement or body law is given. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
universe u

def code (type : Ty) (flow : Expr) (escaped : Word) (fallback : Expr) : Expr :=
  LocalControl.finish type (LocalLoop.toControl type flow escaped) fallback

/-- The actual lexical insertion changes the flow and fallback together. -/
theorem code_rename (type : Ty) (flow : Expr) (escaped : Word) (fallback : Expr) (ξ : Renaming) :
    (code type flow escaped fallback).rename ξ =
      code type (flow.rename ξ) escaped (fallback.rename ξ) := by
  simp [code, LocalControl.finish, LocalLoop.toControl, LanguageResult.bind,
    LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- The function footer keeps the exact expression value or nested failure. -/
theorem terminal_evaluates {catalog : SourceCoreDataCatalog.Catalog}
    {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
    {type : Ty} {faults : RecursiveStageMeaning.FaultRep}
    {actual : Environment} {before after : Store} {flow fallback : Expr}
    {outcome : Staging.Recursive.Outcome} {value : Value}
    (represented : CallableIndexedOwnedAdmittedStagedTerminalStatements.ResultRepresents
      model mapping world sourceType type faults outcome value)
    (evaluated : Evaluates actual before flow value after) (escaped : Word) :
    ∃ result, Evaluates actual before (code type flow escaped fallback) result after ∧
      RecursiveStageMeaning.ResultRepresentsFor model mapping world sourceType type faults outcome result := by
  cases represented with
  | returned payload =>
    exact ⟨_, LocalControl.finish_returned type (LocalLoop.toControl_normal type escaped evaluated), .value payload⟩
  | fault matched =>
    exact ⟨_, LocalControl.finish_failure type (LocalLoop.toControl_failure type escaped evaluated), .fault matched⟩

/-- Both original sum binds have their own strict finite children. The footer
may be generic here; the terminal representation later fixes its outcome. -/
theorem flow_prefix {budget size : Nat} {actual : Environment} {before after : Store}
    {type : Ty} {flow fallback : Expr} {escaped : Word} {value : Value}
    (completed : EvaluationSize size actual before (code type flow escaped fallback) value after)
    (within : size ≤ budget) :
    ∃ flowSize flowValue flowStore,
      EvaluationSize flowSize actual before flow flowValue flowStore ∧ flowSize < budget := by
  change EvaluationSize size actual before (LanguageResult.bind type
    (LocalLoop.toControl type flow escaped)
    (.caseE (.var 0) ((fallback.weakenAt 0).weakenAt 0) (LanguageResult.success (.var 0)))) value after at completed
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed controlTrace strict =>
    change EvaluationSize _ actual before (LanguageResult.bind (LocalControl.controlType type) flow
      (.caseE (.var 0) (LanguageResult.success (.var 0))
        (LanguageResult.failure (LocalControl.controlType type) (.word escaped)))) _ _ at controlTrace
    cases CallableIndirectCallBounds.bind_completed controlTrace (Nat.le_of_lt strict) with
    | failed child childStrict => exact ⟨_, _, _, child, childStrict⟩
    | continued child _remaining childStrict _remainingStrict => exact ⟨_, _, _, child, childStrict⟩
  | continued controlTrace _remaining strict _remainingStrict =>
    change EvaluationSize _ actual before (LanguageResult.bind (LocalControl.controlType type) flow
      (.caseE (.var 0) (LanguageResult.success (.var 0))
        (LanguageResult.failure (LocalControl.controlType type) (.word escaped)))) _ _ at controlTrace
    cases CallableIndirectCallBounds.bind_completed controlTrace (Nat.le_of_lt strict) with
    | continued child _remaining childStrict _remainingStrict => exact ⟨_, _, _, child, childStrict⟩

theorem body_result (type : TypeSystem.Ty) (outcome : Staging.Recursive.Outcome) :
    Staging.Recursive.BodyResult type (control outcome) outcome := by
  cases outcome with
  | value value => exact .returned
  | fault failure => exact .fault

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Actual terminal expression preservation constructs both the sized body
trace and its original BodyResult, then removes the Core control envelope. -/
theorem preserves (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model registry invocation certificate faults budget)
    (escaped : Word) (fallback : Expr)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code lowered.type ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ)
        escaped fallback) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨trace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children child within
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented evaluated escaped
  exact ⟨trace, body_result _ _, result, finalStore, finalMap, finalWorld, whole, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Original footer inversion supplies the strict terminal helper child.
The genuine expression IH constructs its Source body, and determinism retains
the same completed body result and actual endpoint. -/
theorem reflects (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model registry invocation certificate faults budget)
    (escaped : Word) (fallback : Expr)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      (code lowered.type ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) escaped fallback)
      value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      Staging.Recursive.BodyResult node.type (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ := flow_prefix completed within
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children flow (Nat.le_of_lt strict)
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented flow.sound escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic completed.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
