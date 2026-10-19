import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageForSequenceLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeForInitialBounds
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping

/-! Actual Source initializer execution keeps its lexical bindings through the
loop and restores the original scope before the reached suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds SelectedCompilationStageScopedLiftBounds
open CallableIndexedNamedGeneration (source)
open CellAwareSourceFlowReadiness (Ready body_prefix body_ready test_value)

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

open SelectedCompilationStageForInitialBounds (PlainInitial InitialLift)

/-- Only normal for completion reaches the original statement suffix. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId}
    {statement : StatementNode} {test : ExpressionId} {items postItems : List ForItemForm}
    {expected : TypeSystem.Ty} {type : Ty} {initialCode : Expr}
    (sourceEq : invocation.source = source named)
    (initialLift : CellAwareSourceForInitialBounds.InitializersLifts
      (administrative := administrative) (named := named) (context := context) (scope := scope)
      (registry := registry) (invocation := invocation) bridge producer items test postItems statements)
    (initialPreservation : ∀ size, CellAwareScopeForInitialBounds.PreservesAt
      bridge context model named producer registry invocation faults administrative scope items test postItems statements expected type initialCode size)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .forLoop items test postItems statements)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped
    initial admitted authority physical owner sameLocation allocationReady finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have ready : Ready (named := named) (administrative := administrative) (invocation := invocation)
      (context := context) (scope := scope) bridge producer environment canonical actual actualContext embedding before :=
    ⟨mapping,world,store,environments,heaps,locals,agrees,actualTyped,runtime,covers,sameLedger,
      initial,admitted,authority,physical,owner,sameLocation,allocationReady⟩
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedForSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, _headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, _headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _headSmaller, _tailSmaller, executed, tail⟩
  · have loop := SelectedCompilationStageForSourceInversion.fault unique statementFound form failed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((CallableIndexedOwnedAdmittedStagedForSourceBridge.closed lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.returned statementFound form lifted).sound, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted .nil).sound,
            .completed (.fallthrough environment)⟩
  · obtain ⟨rfl, loop⟩ := SelectedCompilationStageForSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageForSourceInversion.fallthrough_environment loop
    obtain ⟨stagedSize, staged, reached, lifted, adapted⟩ := initialLift ready loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, (CallableIndexedOwnedAdmittedStagedForSourceBridge.fault statementFound form lifted).sound,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata, effect,
        last, _, post⟩ := initialPreservation stagedSize environments heaps locals agrees actualTyped
          runtime covers sameLedger initial admitted authority physical owner sameLocation allocationReady lifted
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffixTyped last post (authority.transport effect) (physical.transport effect preserved)
        owner sameLocation allocationReady tail
      obtain ⟨tailGrade, tailMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace liftedTail
      exact ⟨tailContext, tailOutcome, tailHeap,
        (CallableIndexedOwnedAdmittedStagedForSourceBridge.fallthrough statementFound form lifted tailMeasured).sound,
        adaptedTail⟩


end Solcore.SourceSemantics.CoreLowering.CellAwareSourceForSequenceLifting
