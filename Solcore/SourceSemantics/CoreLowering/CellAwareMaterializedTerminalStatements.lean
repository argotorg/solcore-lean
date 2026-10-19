import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedScopeBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedFlowOutput

/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression statements)
  (certified : certificate scope expression lowered)
  (found : invocation.source.lookupExpression? expression = some node)
  (sourceTyped : ExpressionHasType invocation.source context expression node.type)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalInstanceValues.model compiled.indexed) named.signature.key [] mapping world before store environment)
  (physical : CellAwareScopePhysical.Physical compiled named context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CellAwareMaterializedScopeBounds.PreservesBelow
      bridge context model named registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      CellAwareMaterializedFlowOutput.FlowAt compiled finalMap finalWorld owner.key.frameLocation (control outcome) value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalInstanceValues.model compiled.indexed) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, output, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    obtain ⟨raw, same, positive⟩ := output _ rfl
    cases same
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, CellAwareMaterializedFlowOutput.FlowAt.returned positive, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, CellAwareMaterializedFlowOutput.FlowAt.fault, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

end Terminal

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedTerminalStatements
