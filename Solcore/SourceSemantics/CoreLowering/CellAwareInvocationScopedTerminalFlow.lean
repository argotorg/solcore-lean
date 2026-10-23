import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationExpressionBounds

/-! Actual terminal statement composition over the same mixed heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head control ResultRepresents)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {index : ActualBodyInvocation.Index compiled bodyRelation}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificate : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}

section Terminal
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  (head : Head invocation expression mode statements)
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
private theorem preserves_child (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {childSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (child : Staging.Recursive.Size.Expression program registry childSize invocation context environment
      before expression outcome after)
    (within : Staging.Recursive.Size.stepSize [childSize] ≤ budget) :
    Staging.Recursive.Size.StatementsIn program registry mode (Staging.Recursive.Size.stepSize [childSize])
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
private theorem reflects_child (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment)
      bridge context model index registry invocation certificate faults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalLoop.returnValue lowered.type lowered.expression).rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.StatementsIn program registry mode sourceSize invocation context environment
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

section Bounds
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId}
  {statements : List StatementId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {administrative : Core.Context}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))

theorem preserves
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.PreservesBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget) :
    CellAwareInvocationFlowBounds.PreservesAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready
    finalContext bodyOutcome after trace
  obtain ⟨childSize,outcome,rfl,rfl,rfl,child⟩ :=
    CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion.child_of_body unique head trace
  obtain ⟨_trace,value,finalStore,finalMap,finalWorld,evaluated,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    preserves_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children child within
  cases represented with
  | returned payload => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨_,finalStore,finalMap,finalWorld,evaluated,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩

theorem reflects
    (head : Head invocation expression mode statements)
    (found : invocation.source.lookupExpression? expression = some node)
    (sourceTyped : ExpressionHasType invocation.source context expression node.type)
    (certified : certificate scope expression lowered)
    (budget : Nat)
    (children : CellAwareInvocationExpressionBounds.ReflectsBelow (attachment := attachment) bridge context model index registry invocation certificate faults budget) :
    CellAwareInvocationFlowBounds.ReflectsAtMost (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode statements node.type lowered.type
      (LocalLoop.returnValue lowered.type lowered.expression) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees typed _runtime _covers _ledger _sourceSites initial admitted authority physical owner sameLocation _ready completed
  obtain ⟨sourceSize,outcome,after,finalMap,finalWorld,trace,represented,finalHeaps,maps,worlds,
      frame,metadata,effect,reached,related,post⟩ :=
    reflects_child bridge head certified found sourceTyped environments heaps locals agrees typed initial admitted authority physical owner sameLocation
      budget children completed within
  cases represented with
  | returned payload => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.returned payload,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
  | fault matched => exact ⟨sourceSize,context,_,after,finalMap,finalWorld,trace,.fault matched,
      finalHeaps,maps,worlds,frame,metadata,effect,reached,related,post⟩
end Bounds

section Unit
variable {mode : Bool} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : StatementId} {node : StatementNode} {rest : List StatementId}
  (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)))
  (unitValue : ∀ mapping world, model.Represents mapping world .unit .unit .unit .unit)
  (found : invocation.source.lookupStatement? id = some node)
  (form : node.form = .returnStmt none)

include unitValue found form in
theorem unit_preserves (unique : NodeOccurrencesUnique invocation.source) (size : Nat) :
    CellAwareInvocationFlowBounds.PreservesAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl,rfl,rfl⟩ := CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion.return_unit unique found form trace
  refine ⟨_,store,mapping,world,?_,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  · simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  · exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩

include unitValue found form in
theorem unit_reflects (size : Nat) :
    CellAwareInvocationFlowBounds.ReflectsAt (attachment := attachment) bridge context model index producer registry invocation faults
      administrative scope mode (id :: rest) .unit .unit (LocalLoop.returned .unit) size := by
  intro mapping world actualContext environment canonical actual before store embedding value finalStore
    _environments heaps _locals _agrees _typed _runtime _covers _ledger _sourceSites initial admitted
    _authority _physical _owner _sameLocation _ready completed
  have evaluated : Evaluates actual store ((LocalLoop.returned .unit).rename embedding)
      (LocalLoop.returnedValue .unit) store := by
    simpa only [LoopRenaming.returned, Expr.rename] using
      (LocalLoop.returned_evaluates (show Evaluates actual store .unit .unit store from .unit))
  obtain ⟨rfl,rfl⟩ := evaluation_deterministic completed.sound evaluated
  refine ⟨_,context,.returned .unit,before,mapping,world,
    .returnUnit (lookupStatement?_sound found) form,.returned (unitValue mapping world),heaps,.refl _,.refl _,
    .refl _ _,.refl _,.refl _ _ _ _,initial,callerProtocol.refl initial,?_⟩
  exact ⟨admitted.rows,by intro source same; cases same; exact ⟨.unit,admitted.heap⟩⟩
end Unit

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationScopedTerminalFlow
