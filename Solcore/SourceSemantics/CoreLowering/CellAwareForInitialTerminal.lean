import Solcore.SourceSemantics.CoreLowering.CellAwareForHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForSourceBridge
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopProgress
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareForIterations
import Solcore.SourceSemantics.CoreLowering.CellAwareForEntry
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedForReadiness
import Solcore.SourceSemantics.CoreLowering.CoreHelperInversion

/-! The real for-loop prelude and recursive execution compose with the same
mixed state. No Source cell or generalized descriptor is erased when installing
the native recursive closure or restoring its caller. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTerminal
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds (PostAdmission)
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post)
open CellAwareLoopState (Progress)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {projects : GenericHeap.Projection}
  (model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    projects compiled.indexed.layouts.definitions)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) callerProtocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {administrative actualContext : Core.Context} {context : SourceSemantics.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment}
  {ξ : Renaming} {location : Location} {type : Ty} {conditionCode code : Expr} {selfReason : Word}
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before after : Dynamic.Heap} {store : Store}
  {certificate : GenericExpressionMeaning.Certificate} {body : Expr}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}

variable (transport : ProtectedStateTransition.AdministrativeTransport callerProtocol)
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {testCode loopCode postCode : Expr} {postItems : List ForItemForm}
  (booleans : ∀ {mapping world sourceValue nativeValue},
    model.Represents mapping world .bool sourceValue nativeValue .bool →
    ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)

include bridge model producer transport booleans in
theorem preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.PreservesAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final) :
    CellAwareScopeForInitialBounds.PreservesAtMost bridge context model named producer stages invocation faults
      administrative scope [] test postItems statements expected type
      (LocalLoop.iterate type testCode loopCode postCode selfReason) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready outcome after trace
  obtain ⟨loopSize, rawOutcome, sameSize, sameOutcome, loopTrace⟩ :=
    CallableIndexedOwnedAdmittedStagedForInitializerSource.nil trace
  have loopWithin : loopSize ≤ budget := Nat.le_trans (Nat.le_of_lt (by
    simp only [sameSize, Staging.Recursive.Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega)) within
  rw [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore loopTrace] at sameOutcome
  subst outcome
  exact CellAwareForHeads.preserves bridge model producer transport booleans
    children found nodeType typed generated nativeTyped correct postCorrect loopWithin
    environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
    initial admitted authority physical owner sameLocation ready loopTrace

include bridge model producer transport booleans in
theorem reflects {budget : Nat}
    (children : ∀ childSize, childSize < budget → CellAwareScopeExpressionBounds.ReflectsAt bridge context model named stages invocation certificate faults childSize)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.iterate type testCode loopCode postCode selfReason) (LocalLoop.resultType type)
      compiled.indexed.layouts.definitions)
    (correct : CellAwareScopeFlowBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope false statements expected type loopCode budget)
    (postCorrect : CellAwareScopeForPostBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope postItems expected type postCode budget)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (CallableIndexedNamedGeneration.source named) context statements)
    (postTyped : ∃ control final, ForItemsHaveType (CallableIndexedNamedGeneration.source named) control context postItems final) :
    CellAwareScopeForInitialBounds.ReflectsAtMost bridge context model named producer stages invocation faults
      administrative scope [] test postItems statements expected type
      (LocalLoop.iterate type testCode loopCode postCode selfReason) budget := by
  intro size within mapping world actualContext environment canonical actual before store embedding value finalStore
    environments heaps locals agrees actualTyped runtime covers sameLedger initial admitted authority physical owner sameLocation ready completed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
      maps, worlds, frame, metadata, effect, reached, related, post⟩ :=
    CellAwareForHeads.reflects bridge model producer transport booleans
      children found nodeType typed generated nativeTyped correct postCorrect within
      environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped postTyped
      initial admitted authority physical owner sameLocation ready completed
  refine ⟨Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize [], sourceSize], outcome,
    after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata, effect, reached, related, post⟩
  simpa only [CallableIndexedOwnedAdmittedStagedForSourceBridge.loop_restore trace] using
    (CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop Staging.Recursive.Size.ForItems.empty trace)

end Solcore.SourceSemantics.CoreLowering.CellAwareForInitialTerminal
