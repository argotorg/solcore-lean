import Solcore.SourceSemantics.CoreLowering.ProtectedLoopStatementControlShape
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion

/-! Actual break and continue statements have the same independent Source
and staged control outcome, with no heap or physical history change. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head)

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
  {context : SourceSemantics.Context} {certificates : GenericExpressionMeaning.Certificate}

theorem breaking {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
      environment before (id :: rest) finalContext outcome after := by
    cases mode <;> exact trace.sound
  obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.breaking_view unique found form ordinary
  exact ⟨_, _, _, .breaking (lookupStatement?_sound found) form, .completed (.breaking environment)⟩

theorem continuing {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {node : StatementNode} {rest : List StatementId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ordinary : TypedScopedStatements.Executes mode program context invocation.evidence invocation.source
      environment before (id :: rest) finalContext outcome after := by
    cases mode <;> exact trace.sound
  obtain ⟨rfl, rfl, rfl⟩ := ProtectedLoopStatements.continuing_view unique found form ordinary
  exact ⟨_, _, _, .continuing (lookupStatement?_sound found) form, .completed (.continuing environment)⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceTransferLifting
