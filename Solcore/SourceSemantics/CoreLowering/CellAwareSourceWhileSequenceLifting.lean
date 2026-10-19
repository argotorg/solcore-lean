import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageWhileSequenceLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileLifting
import Solcore.SourceSemantics.CoreLowering.CellAwareLoopHeads
import Solcore.SourceSemantics.CoreLowering.CellAwareSourceFlowReadiness
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping

/-! Ordinary Source conditions and exactly the selected branch reach the same
mixed physical continuation. Genuine earlier stage rejection retains its
actual heap and bypasses the remaining branch and suffix. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
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

open SelectedCompilationStageWhileLifting (PlainWhile WhileLift)
variable (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
/-- The actual while head and the reached suffix share one mixed caller state. -/
theorem lifts {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {mode : Bool} {id : StatementId} {rest statements : List StatementId}
    {statement : StatementNode} {test : ExpressionId} {node : ExpressionNode}
    {testCode loopCode : Expr} {certificate : GenericExpressionMeaning.Certificate}
    {expected : TypeSystem.Ty} {type : Ty} {selfReason : Word}
    (sourceEq : invocation.source = source named)
    (booleans : ∀ {mapping world sourceValue nativeValue},
      model.Represents mapping world .bool sourceValue nativeValue .bool →
      ∃ truth, sourceValue = .bool truth ∧ nativeValue = .bool truth)
    (statementFound : invocation.source.lookupStatement? id = some statement)
    (form : statement.form = .whileLoop test statements)
    (found : invocation.source.lookupExpression? test = some node) (nodeType : node.type = .bool)
    (typed : ExpressionHasType invocation.source context test node.type)
    (generated : certificate scope test ⟨.bool,testCode⟩)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      (LocalLoop.whileLoop type testCode loopCode selfReason) (LocalLoop.resultType type) whole.indexed.layouts.definitions)
    (children : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeSourceLiftBounds.LiftsAt bridge context model named registry invocation certificate size)
    (preservation : Dynamic.SourceRuntimeValid program context (source named) → invocation.evidence.Covers context →
      context.solvedRequirements = (CallableIndexedNamedGeneration.context whole.indexed named).solvedRequirements →
      ∀ size, CellAwareScopeExpressionBounds.PreservesAt bridge context model named registry invocation certificate faults size)
    (body : CellAwareSourceFlowLiftBounds.Lifts (named := named) (administrative := administrative)
      (registry := registry) (invocation := invocation) bridge producer context scope false statements)
    (bodyPreservation : ∀ size, CellAwareScopeFlowBounds.PreservesAt bridge context model named producer registry invocation faults
      administrative scope false statements expected type loopCode size)
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
  have bodyTyped := (CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.children
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form).2
  have suffixTyped := CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping.suffix
    (sourceEq ▸ unique) sourceTyped (sourceEq ▸ statementFound) form
  have children := children runtime covers sameLedger
  have preservation := preservation runtime covers sameLedger
  have lift {n : Nat} {plain : Dynamic.ControlOutcome} {reached : Dynamic.Heap}
      (loop : PlainWhile program n invocation context environment before test statements plain reached) :
      WhileLift program registry invocation context environment before test statements plain reached :=
    CellAwareSourceWhileLifting.while_ready bridge producer children preservation booleans found nodeType typed generated
      body bodyPreservation bodyTyped ready loop
  rcases SelectedCompilationStageScopedSourceInversion.head_and_tail unique statementFound
    (by intro expression equal; rw [form] at equal; cases equal) trace with
    ⟨headSize, reason, _headSmaller, rfl, rfl, failed⟩ |
    ⟨headSize, _headSmaller, terminal, executed⟩ |
    ⟨headSize, tailSize, middleContext, nextEnvironment, middle, _headSmaller, _tailSmaller, executed, tail⟩
  · obtain ⟨loopSize, _loopSmaller, loop⟩ := SelectedCompilationStageWhileSourceInversion.fault unique statementFound form failed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | completed matched =>
      cases matched
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
  · obtain ⟨loopSize, _loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched with
      | breaking innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).1 innerEnvironment rfl).elim
      | continuing innerEnvironment => exact ((SelectedCompilationStageLoopOutcomes.while_closed_of_trace lifted).2 innerEnvironment rfl).elim
      | returned value =>
        exact ⟨_, _, _, .whileReturned (lookupStatement?_sound statementFound) form lifted, .completed (.returned value)⟩
      | fault reason =>
        exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted, .completed (.fault reason)⟩
      | fallthrough innerEnvironment =>
        cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
        rcases terminal with terminal | rfl
        · cases terminal
        · exact ⟨_, _, _, .whileFallthrough (lookupStatement?_sound statementFound) form lifted .nil,
            .completed (.fallthrough environment)⟩
  · obtain ⟨loopSize, _loopSmaller, rfl, loop⟩ := SelectedCompilationStageWhileSourceInversion.control unique statementFound form executed
    cases SelectedCompilationStageWhileSourceInversion.fallthrough_environment loop
    obtain ⟨staged, reached, lifted, adapted⟩ := lift loop
    cases adapted with
    | rejected origin call reason finalContext reached =>
      exact ⟨_, _, _, .whileFault (lookupStatement?_sound statementFound) form lifted,
        .rejected origin call reason _ _⟩
    | completed matched =>
      cases matched
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.While.of_trace lifted
      obtain ⟨_, finalStore, finalMap, finalWorld, _, _, finalHeaps, maps, worlds, preserved, metadata, effect,
        last, _, post⟩ := CellAwareLoopHeads.preserves bridge model producer transport booleans
          (fun n _ => preservation n) found nodeType typed generated nativeTyped (fun n _ => bodyPreservation n)
          (Nat.le_refl stagedSize) environments heaps locals agrees actualTyped runtime covers sameLedger bodyTyped
          initial admitted authority physical owner sameLocation allocationReady measured
      obtain ⟨tailContext, tailOutcome, tailHeap, liftedTail, adaptedTail⟩ := remaining
        (environments.extend maps worlds) finalHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
        runtime covers sameLedger suffixTyped last post (authority.transport effect) (physical.transport effect preserved)
        owner sameLocation allocationReady tail
      exact ⟨tailContext, tailOutcome, tailHeap,
        .whileFallthrough (lookupStatement?_sound statementFound) form lifted liftedTail, adaptedTail⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceWhileSequenceLifting
