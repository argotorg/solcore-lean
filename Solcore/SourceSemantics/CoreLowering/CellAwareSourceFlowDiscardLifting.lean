import Solcore.SourceSemantics.CoreLowering.CellAwareScopeExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDiscardInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
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

variable {faults : RecursiveStageMeaning.FaultRep}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode semicolon : Bool} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {expressionNode : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (expressionFound : invocation.source.lookupExpression? expression = some expressionNode)
    (typed : ExpressionHasType invocation.source context expression expressionNode.type)
    (generated : certificates scope expression lowered)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificates size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificates faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner ownerFrame ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have suffix := ProtectedStateImperativeStatementSuffixTyping.discard
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  rcases SelectedCompilationStageDiscardInversion.child_and_tail unique found form discarded trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, tailSize, sourceValue, middle, _strict, _tailStrict, evaluated, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize generated expressionFound typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner ownerFrame evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .expressionFault (lookupStatement?_sound found) form lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
        preservation runtime covers sameLedger stagedSize generated expressionFound typed environments heaps locals agrees actualTyped
          initial admitted authority physical owner ownerFrame measured
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffix middleState post.at_value.2
        (authority.transport effect) (physical.transport effect framePreserved) owner ownerFrame ready tail
      refine ⟨nextContext, result, finalHeap, ?_, restAdapted⟩
      rcases discarded with rfl | rfl
      · exact .discard (lookupStatement?_sound found) form lifted restTrace
      · cases semicolon with
        | false => exact .discardValue (lookupStatement?_sound found) form lifted restTrace
        | true => exact .discard (lookupStatement?_sound found) form lifted restTrace

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowDiscardLifting
