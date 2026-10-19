import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForPostBounds

/-! Independent Source for-loop headers use the same reached mixed state as
ordinary statements. Source and native grades are independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
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

local notation "ReadyAt" => Ready (named := named) (administrative := administrative)
  (invocation := invocation) (context := context) (scope := scope)
  bridge producer environment canonical actual actualContext embedding

def ItemsLifts (items : List ForItemForm) : Prop :=
  ∀ {size : Nat} {environment : Dynamic.Environment} {canonical actual : Environment}
    {actualContext : Core.Context} {embedding : Renaming} {before after : Dynamic.Heap},
    Ready (named := named) (administrative := administrative)
      (invocation := invocation) (context := context) (scope := scope)
      bridge producer environment canonical actual actualContext embedding before →
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome},
      PlainItems program size invocation context environment before items finalContext outcome after →
      ItemsLift program registry invocation context environment before items finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForLiftBounds
