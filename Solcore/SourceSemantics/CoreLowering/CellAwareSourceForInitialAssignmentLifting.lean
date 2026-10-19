import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeBareAssignmentHeads
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForInitialInversion
import Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeStatementSuffixTyping

/-! Independent Source assignment first resolves the original root, then
lifts the real RHS. A completed write supplies the exact mixed state for the
remaining Source flow; an earlier stage rejection retains its reached heap. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedNamedGeneration (source)
open CellAwareSourceForInitialBounds (InitializersLifts)
open CallableIndexedOwnedAdmittedStagedForInitializerSource

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

variable {test : ExpressionId} {postItems : List ForItemForm} {statements : List StatementId}

include transport extension in
theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {rest : List ForItemForm}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (sourceEq : invocation.source = source named)
    (head : GenericAssignmentStatements.Head (.initial compiled.compatible.checked) invocation.source context
      certificate scope administrative compiled.indexed.layouts.definitions assignment operator rhs)
    (bare : assignment.target.projections = [])
    (assignmentTyped : SourceAssignmentHasType invocation.source context assignment operator rhs)
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
    (remaining : InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer rest test postItems statements) :
    InitializersLifts (named := named) (administrative := administrative)
      (registry := stages) (invocation := invocation) (context := context) (scope := scope) bridge producer (.assignValue assignment operator rhs :: rest) test postItems statements := by
  intro size environment canonical actual actualContext embedding before after reachedReady outcome trace
  obtain ⟨mapping, world, store, environments, heaps, locals, agrees, actualTyped, runtime, covers, sameLedger,
    initial, admitted, authority, physical, owner, sameLocation, ready⟩ := reachedReady
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have typed := CallableIndexedOwnedAssignmentAdmission.rhs_typed unique head.found assignmentTyped
  obtain ⟨target, snapshot⟩ := CellAwareScopeBareAssignmentHeads.target_snapshot
    (invocation := invocation) bridge functions extension head bare environments heaps locals agrees initial admitted
  rcases SelectedCompilationStageForInitialInversion.assign snapshot trace with
    ⟨childSize, reason, _strict, rfl, evaluated⟩ |
    ⟨childSize, sourceValue, currentCell, initialValue, currentSelected, _strict, rfl, evaluated,
      currentRead, rootType, rootInitial, pathRead, invalid⟩ |
    ⟨childSize, tailSize, sourceValue, middle, updated, written, _strict, _tailStrict, evaluated, write, tail⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | completed => exact ⟨_, _, _, assignment_operands snapshot measuredChild
        currentRead rootType rootInitial pathRead invalid, .completed (.fault (.invalidAssignmentOperands operator))⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild, .rejected origin call reason _ reached⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ :=
      children runtime covers sameLedger childSize head.right head.found typed
        environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation evaluated
    obtain ⟨measuredSize, measuredChild⟩ := Staging.Recursive.Size.Expression.of_trace lifted
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, _, assignment_fault snapshot measuredChild,
        .rejected origin call reason _ reached⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨middleStore, middleMap, middleWorld, slots, middleHeaps, maps, worlds, framePreserved, metadata,
          effect, _count, nextTyped, ⟨middleState, _related, nextAdmitted⟩, _continuation⟩ :=
        CellAwareScopeBareAssignmentHeads.preserves_value bridge functions extension transport head bare
          environments heaps locals agrees actualTyped initial admitted authority physical owner sameLocation unique assignmentTyped
          (preservation runtime covers sameLedger stagedSize) snapshot measured write
      obtain ⟨nextContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
        ⟨_, _, _, environments.extend maps worlds, middleHeaps, locals.mono metadata,
          DataPlaceChildExpressions.prefix_agrees agrees slots, nextTyped, runtime, covers, sameLedger,
          middleState, nextAdmitted, authority.transport effect, physical.transport effect framePreserved,
          owner, sameLocation, ready⟩ tail
      exact ⟨_, _, finalHeap,
        prepend_assignment snapshot measuredChild write restTrace, restAdapted⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialAssignmentLifting
