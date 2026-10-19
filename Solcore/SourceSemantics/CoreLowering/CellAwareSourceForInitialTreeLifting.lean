import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialProjectedAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAbsentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialOrdinaryLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialDiscardLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareForPostAssignment
import Solcore.SourceSemantics.CoreLowering.CellAwareForPostDiscard
import Solcore.SourceSemantics.CoreLowering.CellAwareForHeaderTree
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedAbsentPrefix
import Solcore.SourceSemantics.CoreLowering.CellAwareNamedOrdinaryPrefix
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedForItemsTyping
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedFlowOutcomes

/-! Post-header declarations, expression effects and actual ordinary writes
retain the mixed heap. Every branch restores the outer lexical observations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
open Core Frontend SourceInference CompatibleEquality GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedFlowOutcomes (Represents Post restore_post)
open CallableIndexedOwnedAdmittedStagedForPostContracts (restoredOutcome)
open CallableIndexedNamedGeneration (source)

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (bindings : ProtectedStateTransition.Bindings protocol)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  (functions : FunctionModel whole.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions whole.indexed))
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : FunctionObservations whole.compatible.checked.catalog functions identities)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial whole.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (compiled : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics namedCode)
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) (GeneralizedLocalInstanceValues.model whole.indexed)))
  {faults : RecursiveStageMeaning.FaultRep}
  (registered : whole.indexed.ancestry.layout.frame.Registered whole.indexed.layouts.definitions)
  (operandIncluded : ∀ reason token,
    GenericAssignmentDiagnostics.OperandRep compiled.own.assignments reason token → faults (.semantic reason) token)
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}

private theorem member_of_root {source : TypedSource} {binder : TypedBinder}
    (declared : SourceCoreDataPlaces.rootBinder source binder.id = .ok binder) :
    binder ∈ SourceCoreDataPlaces.declaredBinders source := by
  have member : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := by
    rw [CompatibleMatchArmScopes.rootBinder_filter declared]
    exact List.mem_cons_self
  exact (List.mem_filter.mp member).1

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension registered faithful observations in
theorem lifts
    (children : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) size)
    (preservation : ∀ context, Dynamic.SourceRuntimeValid program context (source named) →
      invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel whole.compatible.checked receiving functions) named registry invocation
        (certificates context) faults size)
    (sourceEq : invocation.source = source named)
    {administrative : Core.Context} {context finishContext : SourceSemantics.Context}
    {scope finishScope : SourceCoreLocalCell.Scope} {items : List ForItemForm}
    {type : Ty} {code terminal : Expr}
    (tree : CellAwareForHeaderTree.Tree whole.indexed named compiled certificates administrative type
      finishContext finishScope terminal context scope items code)
    (last : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := finishContext) (scope := finishScope) bridge producer [] test postItems statements) :
    CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope) bridge producer items test postItems statements := by
  induction tree with
  | nil => exact last
  | @absent context nextContext scope binder rest body payload
      declaration mono extended ordinary projected allocation annotation same remaining ih =>
    exact CellAwareSourceForInitialAbsentLifting.absent bridge producer registered (body := body)
      (member_of_root declaration) mono extended ordinary projected allocation annotation same sourceEq ih
  | @initialized context nextContext scope binder initializer initializerNode rest lowered body
      declaration mono extended ordinary initializerFound valueType typed certified allocation annotation same remaining ih =>
    exact CellAwareSourceForInitialOrdinaryLifting.initialized bridge producer registered (type := type) (body := body)
      (member_of_root declaration) mono extended ordinary initializerFound valueType typed certified
      allocation annotation same sourceEq (children context) (preservation context) ih
  | @discard context scope expression node rest lowered body found typed certified remaining ih =>
    exact CellAwareSourceForInitialDiscardLifting.lifts bridge producer
      (by simpa only [sourceEq] using found) (by simpa only [sourceEq] using typed) certified
      (children context) (preservation context) ih
  | @assign context scope assignment operator rhs rest body head bare typed operands remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForInitialAssignmentLifting.lifts bridge functions transport extension producer
        rfl head bare typed (children context) (preservation context) ih

  | @assignProjected context scope assignment operator rhs rest body head projected typed _site remaining ih =>
    cases invocation with
    | mk origin actualSource owned stageContext evidence guards =>
      cases sourceEq
      exact CellAwareSourceForInitialProjectedAssignmentLifting.lifts bridge functions faithful observations transport extension producer
        rfl head projected typed (children context) (preservation context) ih

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTreeLifting
