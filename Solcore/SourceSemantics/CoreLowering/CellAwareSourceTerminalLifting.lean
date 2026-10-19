import Solcore.SourceSemantics.CoreLowering.CellAwareSourceBodyLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageTerminalInversion

/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

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

theorem terminal {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {node : ExpressionNode} {statements : List StatementId} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (head : Head invocation id statements)
    (found : invocation.source.lookupExpression? id = some node)
    (typed : ExpressionHasType invocation.source context id node.type)
    (certified : certificates scope id lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size) :
    CellAwareSourceBodyLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope statements := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger _sourceTyped initial admitted authority physical owner ownerFrame _ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := by simpa only [sourceEq] using runtime.graph.nodeOccurrencesUnique
  have terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal invocation.source id statements := by
    cases head with
    | returning rest contains form => exact .returning rest (lookupStatement?_complete unique contains) form
    | tail contains form => exact .tail (lookupStatement?_complete unique contains) form
  obtain ⟨childSize, childOutcome, _strict, rfl, rfl, child⟩ :=
    SelectedCompilationStageTerminalInversion.child_of_body unique terminal trace
  exact SelectedCompilationStageBodyLiftBounds.terminal_expression head
    (children runtime covers sameLedger childSize certified found typed environments heaps locals agrees actualTyped
      initial admitted authority physical owner ownerFrame child)

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceTerminalLifting
