import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds

/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open SelectedCompilationStageBodyLiftBounds

variable {whole : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header whole program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key whole program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog whole.compatible.checked.catalog)
    projects whole.indexed.layouts.definitions}
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog whole.compatible.checked.catalog) protocol whole.indexed.layouts
    whole.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel model (GeneralizedLocalInstanceValues.model whole.indexed)))
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {faults : RecursiveStageMeaning.FaultRep}
  {administrative : Core.Context} {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}

open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)
open SelectedCompilationStageForLiftBounds (PlainItems ItemsLift PlainFor ForLift)
variable {certificate : GenericExpressionMeaning.Certificate}
  {test : ExpressionId} {node : ExpressionNode} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {testCode loopCode postCode : Expr} {post : List ForItemForm}
variable {environment : Dynamic.Environment} {canonical actual : Environment}
  {actualContext : Core.Context} {embedding : Renaming}

open CellAwareSourceForLiftBounds (ItemsLifts)
open CellAwareSourceWhileLifting (body_continue_ready)

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

theorem lifts
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ childSize, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate childSize)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ childSize, CellAwareScopeExpressionBounds.PreservesAt
      bridge context model named registry invocation certificate faults childSize)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (found : invocation.source.lookupExpression? test = some node)
    (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool, testCode⟩)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
    (bodyTyped : ProtectedStateImperativeTypedSourceSites.Statements (source named) context statements)
    (postLift : ItemsLifts (named := named) (administrative := administrative) (context := context)
      (scope := scope) (registry := registry) (invocation := invocation) bridge producer post)
    (postPreservation : ∀ size, CellAwareScopeForPostBounds.PreservesAt bridge context model named producer
      registry invocation faults administrative scope post expected type postCode size)
    (postTyped : ∃ control final, ForItemsHaveType (source named) control context post final)
 : CellAwareSourceForInitialBounds.InitializersLifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) (context := context) (scope := scope)
      bridge producer [] test post statements := by
  intro size environment canonical actual actualContext embedding before after ready outcome trace
  have current := ready
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, allocationReady⟩ := current
  cases trace with
  | initializerFault failed => cases failed
  | loop initial loop =>
    cases initial
    obtain ⟨staged, reached, lifted, adapted⟩ := CellAwareSourceForLifting.for_ready bridge producer
      (children runtime covers sameLedger) (preservation runtime covers sameLedger)
      booleans found nodeType typed generated body bodyPreservation bodyTyped postLift postPreservation postTyped ready loop
    obtain ⟨grade, measured⟩ := Staging.Recursive.Size.ForLoop.of_trace lifted
    refine ⟨_, _, reached, CallableIndexedOwnedAdmittedStagedForHeadContracts.Trace.loop .empty measured, ?_⟩
    cases adapted with
    | completed matched => cases matched <;> exact .completed (by constructor)
    | rejected origin call reason finalContext reached => exact .rejected origin call reason _ _

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialTerminal
