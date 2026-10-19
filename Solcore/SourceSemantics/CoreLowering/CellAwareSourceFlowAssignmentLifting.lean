import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageAssignmentInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {protocol : ProtectedStateTransition.Protocol (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) protocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)
  {receiving : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry receiving)
  {named : SourceCoreGeneralFunctions.Function}
  (producer : ProtectedStateTransition.CellAllocation.Producer
    (catalog := CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) protocol compiled.indexed.layouts
    compiled.indexed.ancestry.layout.frame
    (GeneralizedLocalDescriptorHeap.cellModel
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
      (GeneralizedLocalInstanceValues.model compiled.indexed)))
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

include transport extension in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions)
        named stages invocation certificate faults size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner sameLocation ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have assignmentTyped := ProtectedStateImperativeTypedSourceSites.assignment unique
    (sourceEq.symm ▸ ProtectedStateImperativeTypedSourceSites.head sourceTyped) found form
  have suffix := ProtectedStateImperativeStatementSuffixTyping.assignment
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases SelectedCompilationStageAssignmentInversion.child_and_tail unique found form snapshot trace with
    ⟨childSize, reason, _strict, rfl, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, _strict, rfl, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, _strict, _tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | completed => exact ⟨_, _, _, .assignBareOperands (lookupStatement?_sound found) form snapshot lifted
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, .assignBareFault (lookupStatement?_sound found) form snapshot lifted,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          (preservation runtime covers sameLedger stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        (environments.extend maps worlds) middleHeaps (locals.mono metadata)
        (DataPlaceChildExpressions.prefix_agrees agrees slots) nextTyped runtime covers sameLedger suffix
        middleState nextAdmitted (authority.transport effect) (physical.transport effect framePreserved) owner sameLocation ready tail
      exact ⟨nextContext, result, finalHeap,
        .assignBare (lookupStatement?_sound found) form snapshot lifted write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowAssignmentLifting
