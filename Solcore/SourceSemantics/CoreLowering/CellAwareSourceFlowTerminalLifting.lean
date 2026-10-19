import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedTerminalInversion

/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
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

theorem nil {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool} :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode [] := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped _runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.nil trace
  exact ⟨_, .fallthrough environment, _, .nil, .completed (.fallthrough environment)⟩

theorem return_unit {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node) (form : node.form = .returnStmt none) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    _environments _heaps _locals _agrees _actualTyped runtime _covers _sameLedger _sourceTyped
    _initial _admitted _authority _physical _owner _sameLocation _ready finalContext outcome after trace
  obtain ⟨rfl, rfl, rfl⟩ := SelectedCompilationStageScopedTerminalInversion.return_unit
    (sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique) found form trace
  exact ⟨_, .returned .unit, _, .returnUnit (lookupStatement?_sound found) form, .completed (.returned .unit)⟩

theorem terminal {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope} {mode : Bool}
    {id : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (head : Head invocation id mode statements)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    (certified : certificates scope id lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner ownerFrame _ready
    finalContext outcome after trace
  obtain ⟨childSize, plain, _strict, rfl, rfl, evaluated⟩ :=
    SelectedCompilationStageScopedTerminalInversion.child_of_body
      (sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique) head trace
  have lifted := children runtime covers sameLedger childSize certified found typed
    environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
  obtain ⟨stagedSize, staged, reached, stagedTrace, adapted⟩ := lifted.sized
  refine ⟨_, _, reached, (head.trace stagedTrace).sound, ?_⟩
  cases adapted with
  | completed => cases plain with
    | value value => exact .completed (.returned value)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason reached => exact .rejected origin call reason _ reached

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowTerminalLifting
