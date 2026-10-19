import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalBody
import Solcore.SourceSemantics.CoreLowering.CellAwareStagedTerminalStatements

/-! The actual terminal footer preserves and reflects the mixed heap and
reached caller supplied by its genuine expression child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareStagedTerminalBody
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control)
open CallableIndexedOwnedAdmittedStagedTerminalBody (code flow_prefix terminal_evaluates body_result)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  {model : GenericHeap.PayloadModel catalog projects definitions}
  {cells : GenericHeap.CellModel definitions}
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
  (heaps : GenericHeap.CellHeapRepresents cells mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Actual terminal expression preservation constructs both the sized body
trace and its original BodyResult, then removes the Core control envelope. -/
theorem preserves (budget : Nat)
    (children : CellAwareStagedExpressionBounds.PreservesBelow
      bridge context model cells registry invocation certificate faults budget)
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
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨trace, value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareStagedTerminalStatements.preserves bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children child within
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented evaluated escaped
  exact ⟨trace, body_result _ _, result, finalStore, finalMap, finalWorld, whole, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted in
/-- Original footer inversion supplies the strict terminal helper child.
The genuine expression IH constructs its Source body, and determinism retains
the same completed body result and actual endpoint. -/
theorem reflects (budget : Nat)
    (children : CellAwareStagedExpressionBounds.ReflectsBelow
      bridge context model cells registry invocation certificate faults budget)
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
      GenericHeap.CellHeapRepresents cells finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  obtain ⟨flowSize, flowValue, flowStore, flow, strict⟩ := flow_prefix completed within
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related, post⟩ :=
    CellAwareStagedTerminalStatements.reflects bridge head certified found sourceTyped
      environments heaps locals agrees typed initial admitted budget children flow (Nat.le_of_lt strict)
  obtain ⟨result, whole, resultRep⟩ := terminal_evaluates represented flow.sound escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic completed.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareStagedTerminalBody
