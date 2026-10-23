import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds

/-! Return and tail-expression execution at an actual named or contextual body.
The same stored descriptors, captured frame and heap survive either outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
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
  (heaps : GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) index.owner index.active mapping world before store environment)
  (physical : CellAwareInvocationPhysical.Physical (attachment := attachment) compiled index context scope canonical mapping world before store environment)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (sameLocation : owner.key.frameLocation = physical.location)

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- The real parent step gives a strict expression grade. The expression IH
runs once and the existing return helper preserves its exact endpoint. -/
theorem preserves (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.Statements program registry (Staging.Recursive.Size.stepSize [childSize])
      invocation context environment before statements context (control outcome) after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have strict : childSize < budget :=
    Nat.lt_of_lt_of_le (Staging.Recursive.Size.child_lt_stepSize (child := childSize)
      (children := [childSize]) (by simp)) within
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    children childSize strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
  refine ⟨head.trace child, ?_⟩
  cases represented with
  | value payload =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_success _ evaluated,
      .returned payload, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld,
      by rw [LoopRenaming.returnValue]; exact LocalLoop.returnValue_failure _ evaluated,
      .fault matched, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩

include head certified found sourceTyped environments heaps locals agrees typed admitted authority physical sameLocation in
/-- Native inversion uses the original sum bind and its strict child grade.
The Source result and parent grade are reconstructed from that one child IH. -/
theorem reflects (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements program registry sourceSize invocation context environment
        before statements context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.CellHeapRepresents (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment) mapping world before store finalMap finalWorld after finalStore ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context node.type outcome reached := by
  have original := completed
  rw [LoopRenaming.returnValue] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType lowered.type) (lowered.expression.rename ξ)
      (LocalLoop.returned (.var 0))) value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original within with
  | failed child strict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | fault matched =>
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .fault matched,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  | continued child remaining strict _remainingStrict =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
        maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
      children _ strict certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation child
    cases represented with
    | value payload =>
      have expected := LocalLoop.returnValue_success lowered.type child.sound
      obtain ⟨same, stores⟩ := evaluation_deterministic original.sound expected
      cases same
      subst stores
      exact ⟨_, _, after, finalMap, finalWorld, head.trace trace, .returned payload,
        finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
end Terminal

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationTerminalStatements
