import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowLiftBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
import Solcore.SourceSemantics.CoreLowering.CellAwareScopeFlowBounds

/-! A real return or tail expression preserves the ordinary Source outcome,
or propagates its actual earlier stage rejection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
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

open SelectedCompilationStageScopedLiftBounds (PlainStatements)
variable {faults : RecursiveStageMeaning.FaultRep}

theorem lifts {administrative : Core.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId} {node : StatementNode}
    {expected : TypeSystem.Ty} {type : Ty} {innerCode : Expr}
    (sourceEq : invocation.source = source named)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (inner : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (preservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type innerCode size)
    (remaining : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode rest) :
    CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope mode (id :: rest) := by
  intro size mapping world actualContext environment canonical actual before store embedding
    environments heaps locals agrees actualTyped runtime covers sameLedger sourceTyped initial admitted authority physical owner ownerFrame ready
    finalContext outcome after trace
  have unique : NodeOccurrencesUnique invocation.source := sourceEq.symm ▸ runtime.graph.nodeOccurrencesUnique
  have innerTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.inner
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ found) form
  have notTail : ∀ expression, node.form ≠ .expression expression false := by
    intro expression same
    rw [form] at same
    cases same
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique found notTail trace with
    ⟨headSize, reason, strict, contextEq, outcomeEq, failed⟩ |
    ⟨headSize, strict, stopped, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, strict, tailStrict, executed, tail⟩
  · subst finalContext
    subst outcome
    obtain ⟨innerSize, innerContext, innerStrict, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_fault unique found form failed
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner ownerFrame ready
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext (.fault reason) after from .fault innerTrace)
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, outcomeEq, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst finalContext
    subst outcome
    obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
      environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
      initial admitted authority physical owner ownerFrame ready
      (show PlainStatements program false innerSize invocation context environment before statements
        innerContext innerOutcome after from .control innerTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
    | completed matched =>
      cases matched with
      | returned value =>
        exact ⟨context, _, _, .blockReturned (lookupStatement?_sound found) form lifted, .completed (.returned value)⟩
      | breaking innerEnvironment =>
        exact ⟨context, _, _, .blockBreaking (lookupStatement?_sound found) form lifted, .completed (.breaking environment)⟩
      | continuing innerEnvironment =>
        exact ⟨context, _, _, .blockContinuing (lookupStatement?_sound found) form lifted, .completed (.continuing environment)⟩
      | fault reason =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        rcases stopped with impossible | rfl
        · cases impossible
        · exact ⟨context, _, _, .blockFallthrough (lookupStatement?_sound found) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨innerSize, innerContext, innerOutcome, innerStrict, contextEq, restored, innerTrace⟩ :=
      SelectedCompilationStageScopedSourceInversion.block_control unique found form executed
    subst middleContext
    cases innerOutcome with
    | fallthrough innerEnvironment =>
      simp only [Dynamic.restoreControl, Dynamic.ControlOutcome.fallthrough.injEq] at restored
      subst nextEnvironment
      obtain ⟨nextContext, staged, reached, lifted, adapted⟩ := inner
        environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
        initial admitted authority physical owner ownerFrame ready
        (show PlainStatements program false innerSize invocation context environment before statements
          innerContext (.fallthrough innerEnvironment) middle from .control innerTrace)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨context, _, _, .blockFault (lookupStatement?_sound found) form lifted, .rejected origin call reason context reached⟩
      | completed matched =>
        cases matched
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.StatementsIn.of_trace lifted
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, framePreserved, metadata, effect, middleState, _related, post⟩ :=
          preservation stagedSize environments heaps locals agrees actualTyped runtime covers sameLedger innerTyped
            initial admitted authority physical owner ownerFrame ready measured
        obtain ⟨lastContext, result, finalHeap, restTrace, restAdapted⟩ := remaining
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          runtime covers sameLedger suffixTyped middleState post
          (authority.transport effect) (physical.transport effect framePreserved) owner ownerFrame ready tail
        exact ⟨lastContext, result, finalHeap, .blockFallthrough (lookupStatement?_sound found) form lifted restTrace,
          restAdapted⟩

    | returned value => cases restored
    | breaking environment => cases restored
    | continuing environment => cases restored
    | fault reason => cases restored

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowBlockLifting
