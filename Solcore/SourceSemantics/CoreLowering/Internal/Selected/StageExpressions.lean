import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedConditionalHeads
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PhysicalCalls
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedExpressionSequence
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBuiltinCallBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedArgumentTraceBounds
import Solcore.SourceSemantics.CoreLowering.CallablePreparedOperatorSourceBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedProxyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGroupBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ExpressionBounds
import Solcore.SourceSemantics.Staging.RecursiveAtomicLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndexHeadBounds
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CatalogOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedCoercionChain
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRawDirectAuthority

/-!
# Lifting to staged Source: expressions

Bounds of expression lifting, and lifting of sequences, reads, groups, indices, constructors, builtins, operators, conditionals and direct calls.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedStagedNamedChildBounds (poolBridge)
open Staging.Recursive

/-- Each ordinary control outcome embeds into the staged body unchanged.
The enclosing loop or function exit consumes its own control transfers. -/
inductive BodyEmbeds : Dynamic.ControlOutcome → BodyOutcome → Prop where
  | returned (value) : BodyEmbeds (.returned value) (.returned value)
  | fallthrough (environment) : BodyEmbeds (.fallthrough environment) (.fallthrough environment)
  | breaking (environment) : BodyEmbeds (.breaking environment) (.breaking environment)
  | continuing (environment) : BodyEmbeds (.continuing environment) (.continuing environment)
  | fault (reason) : BodyEmbeds (.fault reason) (.fault (.semantic reason))

/-- Completed bodies keep their exact final context and heap. A stage stop
keeps the context and heap of its actual earlier staged prefix. -/
inductive BodyAdapted (plainFinal : SourceSemantics.Context)
    (plain : Dynamic.ControlOutcome) (plainAfter : Dynamic.Heap) :
    SourceSemantics.Context → BodyOutcome → Dynamic.Heap → Prop where
  | completed {staged} (matched : BodyEmbeds plain staged) :
      BodyAdapted plainFinal plain plainAfter plainFinal staged plainAfter
  | rejected (origin : Scope) (call : ExpressionId) (reason : Staging.CallGuard.Fault)
      (finalContext : SourceSemantics.Context) (reached : Dynamic.Heap) :
      BodyAdapted plainFinal plain plainAfter finalContext (.fault (.stage origin call reason)) reached

def BodyLift (program : Program) (registry : Registry) (mode : Bool) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (statements : List StatementId)
    (plainFinal : SourceSemantics.Context) (plain : Dynamic.ControlOutcome)
    (plainAfter : Dynamic.Heap) : Prop :=
  ∃ finalContext staged reached,
    StatementsIn program registry mode invocation context environment before statements
      finalContext staged reached ∧ BodyAdapted plainFinal plain plainAfter finalContext staged reached

def terminalControl (plain : Dynamic.ExpressionOutcome) : Dynamic.ControlOutcome :=
  match plain with
  | .value value => .returned value
  | .fault reason => .fault reason

/-- A lifted terminal expression keeps the literal return envelope. -/
theorem terminal_expression {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {expression : ExpressionId} {statements : List StatementId}
    {plain : Dynamic.ExpressionOutcome}
    (head : CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression statements)
    (lifted : Lifting.ExpressionLift program registry invocation context environment
      before expression plain after) :
    BodyLift program registry true invocation context environment before statements context
      (terminalControl plain) after := by
  obtain ⟨size, staged, reached, trace, adapted⟩ := lifted.sized
  refine ⟨context, _, reached, (head.trace trace).sound, ?_⟩
  cases adapted with
  | completed => cases plain with
    | value value => exact .completed (.returned value)
    | fault reason => exact .completed (.fault reason)
  | rejected origin call reason reached => exact .rejected origin call reason context reached

/-- The original function exit rule converts an exact body completion. A
stage stop propagates its own origin, occurrence and reached heap. -/
theorem BodyAdapted.exit {plainFinal finalContext : SourceSemantics.Context}
    {plain : Dynamic.ControlOutcome} {plainAfter reached : Dynamic.Heap}
    {staged : BodyOutcome} {expected : TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (adapted : BodyAdapted plainFinal plain plainAfter finalContext staged reached)
    (exit : CompatibleNamedBody.Exit expected plain outcome) :
    ∃ result, BodyResult expected staged result ∧ Lifting.Adapted outcome plainAfter result reached := by
  cases adapted with
  | completed matched =>
    cases matched with
    | returned value => cases exit; exact ⟨_, .returned, .completed⟩
    | fallthrough environment =>
      cases exit with
      | unit same => subst expected; exact ⟨_, .unit, .completed⟩
    | fault reason => cases exit; exact ⟨_, .fault, .completed⟩
    | breaking environment => cases exit; exact ⟨_, .breaking, .completed⟩
    | continuing environment => cases exit; exact ⟨_, .continuing, .completed⟩
  | rejected origin call reason finalContext reached =>
    exact ⟨_, .fault, .rejected origin call reason reached⟩

theorem BodyLift.global {program : Program} {registry : Registry} {caller child : Scope}
    {context bodyContext plainFinal : SourceSemantics.Context}
    {before bound after : Dynamic.Heap} {function : Dynamic.GlobalFunction}
    {body : Dynamic.BodyInstance} {roots : List StatementId} {types : List TypeSystem.Ty}
    {environment : Dynamic.Environment} {arguments : List Dynamic.Value}
    {plain : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    (instantiates : Dynamic.FunctionInstantiates program function.instantiation body)
    (covers : function.evidence.Covers body.context)
    (rootsEq : Dynamic.StatementRoots body.source.roots roots)
    (selected : registry.Closure (globalView body function.evidence roots) child)
    (parameters : MonoBindersExtend body.source.owner body.context body.source.inputs types bodyContext)
    (allocate : Dynamic.BindersAllocate [] before body.source.inputs arguments environment bound)
    (lifted : BodyLift program registry true child bodyContext environment bound roots plainFinal plain after)
    (exit : CompatibleNamedBody.Exit body.resultType plain outcome) :
    Lifting.ApplicationLift program registry caller context before (.global function) arguments outcome after := by
  obtain ⟨finalContext, staged, reached, trace, adapted⟩ := lifted
  obtain ⟨result, converted, resultAdapted⟩ := adapted.exit exit
  exact ⟨result, reached, .global instantiates covers rootsEq selected parameters allocate trace converted,
    resultAdapted⟩

theorem BodyLift.closure {program : Program} {registry : Registry} {caller child : Scope}
    {context bodyContext plainFinal : SourceSemantics.Context}
    {before copied bound after : Dynamic.Heap} {function : Dynamic.Closure} {types : List TypeSystem.Ty}
    {entry environment : Dynamic.Environment} {arguments : List Dynamic.Value}
    {plain : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    (selected : registry.Closure function child)
    (valid : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters types bodyContext)
    (copy : Dynamic.EnvironmentCopies function.source function.captured before entry copied)
    (allocate : Dynamic.BindersAllocate entry copied function.parameters arguments environment bound)
    (lifted : BodyLift program registry true child bodyContext environment bound function.body plainFinal plain after)
    (exit : CompatibleNamedBody.Exit function.resultType plain outcome) :
    Lifting.ApplicationLift program registry caller context before (.closure function) arguments outcome after := by
  obtain ⟨finalContext, staged, reached, trace, adapted⟩ := lifted
  obtain ⟨result, converted, resultAdapted⟩ := adapted.exit exit
  exact ⟨result, reached, .closure selected valid parameters copy allocate trace converted, resultAdapted⟩

/-- The body port starts at the same actual physical parameter entry as the
existing preservation port. Its recursive premise is internal to the root proof. -/
def NamedLiftsBelow {compiled : SourceCoreUnifiedCompilation.Compiled}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (header : Header compiled (Program.ofChecked compiled.sourceProgram))
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
    (stages : Registry) (child : Scope) (budget : Nat) : Prop :=
  ∀ {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming},
    DataHeap.EnvRepresents catalog mapping world administrative
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before header.context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
    ∀ initial : State headers keys
      ⟨header.bindings.reverse.map (fun binding => (binding.1.id, binding.2)), mapping, world, before, store, canonical⟩,
    Admission (poolBridge (headers := headers) (keys := keys)) header.context initial →
    ∀ owner : OwnedKey keys,
    (owner.key.capturePrefix = 0 → header.globals = compiled.indexed.base.globals.length →
      CallableIndexedOwnedNestedCanonicalState.Packet owner header _ initial) →
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) canonical →
    ∀ {size : Nat} {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome}
      {after : Dynamic.Heap},
    RecursiveNamedCallBounds.FunctionOutcome (Program.ofChecked compiled.sourceProgram) size
      header.context child.evidence child.source environment before header.function.body finalContext outcome after →
    size ≤ budget →
    BodyLift (Program.ofChecked compiled.sourceProgram) stages true child header.context environment
      before header.function.body finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageBodyLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageBodyLiftBounds
universe u

/-- The original function and scoped statement relations retain their distinct
execution modes and all ordinary control outcomes. -/
def PlainStatements (program : Program) (mode : Bool) (size : Nat)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (statements : List StatementId)
    (finalContext : SourceSemantics.Context) (outcome : Dynamic.ControlOutcome)
    (after : Dynamic.Heap) : Prop :=
  if mode then RecursiveNamedCallBounds.FunctionOutcome program size context invocation.evidence
    invocation.source environment before statements finalContext outcome after
  else RecursiveNamedCallBounds.StatementsOutcome program size context invocation.evidence
    invocation.source environment before statements finalContext outcome after

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {administrative : Core.Context}
  (condition : Location → NativeFrame → Prop)
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A scoped compiler child starts at its genuine physical entry. Every
recursive use is discharged by the internal sized body induction. -/
def FlowLifts (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) (mode : Bool)
    (statements : List StatementId) (budget : Nat) : Prop :=
  ∀ {size : Nat}, size ≤ budget →
  ∀ {mapping : LocationMap} {world : StoreTyping} {actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {contextLocation : Location} {native : NativeFrame}
    (_environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrative scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (_agrees : EnvironmentsAgree ξ canonical actual)
    (_actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (_reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (_read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (_unmapped : contextLocation ∉ mapping)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (_conditioned : condition contextLocation native)
    (_admitted : Admission bridge context initial),
    ∀ {finalContext : SourceSemantics.Context} {outcome : Dynamic.ControlOutcome} {after : Dynamic.Heap},
      PlainStatements program mode size invocation context environment before
        statements finalContext outcome after →
    BodyLift program stages mode invocation context environment before statements
      finalContext outcome after

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
open Frontend SourceInference
open SelectedCompilationStageScopedLiftBounds (PlainStatements)

/-- The original non-tail statement either stops or reaches its actual suffix.
Singleton function bodies retain their original statement result. -/
theorem head_and_tail {program : Program} {mode : Bool} {invocation : Staging.Recursive.Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (notTail : ∀ expression, node.form ≠ .expression expression false)
    (trace : PlainStatements program mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ headSize reason, headSize < size ∧ finalContext = context ∧ outcome = .fault reason ∧
      SourceExecutionSize.StatementFaults program headSize context invocation.evidence invocation.source
        environment before id reason after) ∨
    (∃ headSize, headSize < size ∧ (Dynamic.TerminalControl outcome ∨ rest = []) ∧
      SourceExecutionSize.StatementExecutes program headSize context invocation.evidence invocation.source
        environment before id finalContext outcome after) ∨
    (∃ headSize tailSize middleContext nextEnvironment middle,
      headSize < size ∧ tailSize < size ∧
      SourceExecutionSize.StatementExecutes program headSize context invocation.evidence invocation.source
        environment before id middleContext (.fallthrough nextEnvironment) middle ∧
      PlainStatements program mode tailSize invocation middleContext nextEnvironment middle
        rest finalContext outcome after) := by
  have sameNode : ∀ {other}, ContainsStatement invocation.source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases mode with
  | false =>
    change RecursiveNamedCallBounds.StatementsOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | cons head tail =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .control tail⟩)
      | terminal head stopped =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inl stopped, head⟩)
    | fault failed =>
      cases failed with
      | head failed =>
        exact .inl ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, failed⟩
      | tail head failed =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .fault failed⟩)
  | true =>
    change RecursiveNamedCallBounds.FunctionOutcome _ _ _ _ _ _ _ _ _ _ _ at trace
    cases trace with
    | control executed =>
      cases executed with
      | tailExpression actual same _ =>
        cases sameNode actual
        exact False.elim (notTail _ same)
      | singleton _ _ head =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inr rfl, head⟩)
      | cons head tail =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .control tail⟩)
      | terminal head stopped =>
        exact .inr (.inl ⟨_, SourceExecutionSize.child_lt_stepSize (by simp), .inl stopped, head⟩)
    | fault failed =>
      cases failed with
      | tailExpression actual same _ =>
        cases sameNode actual
        exact False.elim (notTail _ same)
      | singleton failed | head failed =>
        exact .inl ⟨_, _, SourceExecutionSize.child_lt_stepSize (by simp), rfl, rfl, failed⟩
      | tail head failed =>
        exact .inr (.inr ⟨_, _, _, _, _, SourceExecutionSize.child_lt_stepSize (by simp),
          SourceExecutionSize.child_lt_stepSize (by simp), head, .fault failed⟩)

/-- A block restores its outer lexical context and control environment while
retaining the exact inner trace and reached heap. -/
theorem block_control {program : Program} {source : TypedSource}
    {context finalContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {body : List StatementId}
    {size : Nat} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (trace : SourceExecutionSize.StatementExecutes program size context evidence source
      environment before id finalContext outcome after) :
    ∃ innerSize innerContext innerOutcome,
      innerSize < size ∧ finalContext = context ∧ outcome = Dynamic.restoreControl environment innerOutcome ∧
      SourceExecutionSize.StatementsExecute program innerSize context evidence source environment before
        body innerContext innerOutcome after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace <;> have same := sameNode (by assumption) <;> subst_vars <;> simp_all
  refine ⟨_, ?_, _, _, rfl, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

theorem block_fault {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {body : List StatementId}
    {size : Nat} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (trace : SourceExecutionSize.StatementFaults program size context evidence source
      environment before id reason after) :
    ∃ innerSize innerContext, innerSize < size ∧
      SourceExecutionSize.StatementsFault program innerSize context evidence source environment before
        body innerContext reason after := by
  have sameNode : ∀ {other}, ContainsStatement source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace
  case missing absent => exact False.elim (Dynamic.StatementAbsentIn.excludes_contains absent (lookupStatement?_sound found))
  all_goals have same := sameNode (by assumption)
  all_goals subst_vars; simp_all
  refine ⟨_, ?_, _, by assumption⟩
  exact SourceExecutionSize.child_lt_stepSize (by simp)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageScopedSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
/-! An ordinary named invocation enters the same authenticated physical
parameter frame. The selected body lift retains its exact captured state. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedParameterCertificates CallableIndexedParameterMeaning RecursiveNamedCatalog
open RecursiveNamedCatalogInvocationBounds CallableIndexedOwnedFunctionState
open CallableIndexedOwnedInvocationBounds CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedFunctionValues (Header NamedCapture NamedSourceAt)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow BodyLift)
open Staging.Recursive.Lifting (ApplicationLift)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

theorem source_prefix
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD function)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (arity : header.function.parameters.length = arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence function.evidence before (.global function) arguments outcome after) :
    ∃ bodySize environment bound,
      Dynamic.BindersAllocate [] before header.function.parameters arguments environment bound ∧
      RecursiveNamedCallBounds.BodyTrace (Program.ofChecked compiled.sourceProgram) bodySize
        header.function header.context environment bound outcome after ∧ bodySize < size := by
  have canonical : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size
      context callerEvidence header.function.evidence before
      (.global ⟨function.instantiation, header.function.evidence⟩) arguments outcome after := by
    simpa only [sourceAt.dictionary] using trace
  obtain ⟨bodySize, bodyTrace, bodySmaller⟩ := RecursiveNamedCallBounds.source_call_body
    owners sourceAt.frame arity canonical
  obtain ⟨childSize, environment, bound, allocated, statements, smaller⟩ :=
    RecursiveNamedCallBounds.body_trace sourceAt.frame header.extended arity bodyTrace
  exact ⟨childSize, environment, bound, allocated, statements, Nat.lt_trans smaller bodySmaller⟩

theorem body_control {program : Program} {function : Dynamic.Closure} {size : Nat}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (trace : RecursiveNamedCallBounds.BodyTrace program size function context environment before outcome after) :
    ∃ finalContext control,
      RecursiveNamedCallBounds.FunctionOutcome program size context function.evidence function.source
        environment before function.body finalContext control after ∧
      CompatibleNamedBody.Exit function.resultType control outcome := by
  cases trace with
  | returned execution => exact ⟨_, _, .control execution, .returned _⟩
  | unit same execution => exact ⟨_, _, .control execution, .unit _ same⟩
  | fault failed => exact ⟨_, _, .fault failed, .fault _⟩
  | escaped execution escape =>
    rcases escape with ⟨environment, rfl⟩ | ⟨environment, rfl⟩
    · exact ⟨_, _, .control execution, .breaking environment⟩
    · exact ⟨_, _, .control execution, .continuing environment⟩

private theorem related_cast_frame
    {initial : ProtectedStateTransition.Index} (saved : State headers keys initial)
    {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
    {first second : Location} {next : Value} (same : first = second)
    (state : State headers keys ⟨scope, mapping, world, heap, store.set first next, canonical⟩)
    (related : Relates saved state) :
    Relates saved (Eq.mp (congrArg (fun location => State headers keys
      ⟨scope, mapping, world, heap, store.set location next, canonical⟩) same) state) := by
  cases same
  exact related

private theorem readyAt_cast
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    {first second : SourceCoreAllocationLayouts.Prepared}
    {frame : SourceCoreCallableIndexedFrames.Layout}
    (same : first = second)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys) second frame model)
    {location : Location} {native : NativeFrame}
    (ready : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary location native) :
    ProtectedStateTransition.OrdinaryAllocation.ReadyAt
      ((same.symm ▸ producer).toOrdinary) location native := by
  cases same
  exact ready
variable
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (header : Header compiled (Program.ofChecked compiled.sourceProgram))
  (physicalCapture : CallableIndexedOwnedNamedPhysicalCaptures.Capture headers owner.key header mapping world store)
variable {arguments : List Dynamic.Value} {payloads : List Value}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : NamedSourceAt header rawD function)

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)


include functions owner caller header physicalCapture sourceAt in
theorem lifts_invocation
    (sameLayouts : header.layouts = compiled.indexed.layouts)
    (physicalAuthority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
    (member : header ∈ headers)
    (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
    (certified : SelectedCompilationNamedSourceTyping.Certified header)
    (stable : StableRows caller)
    (heapTyped : Dynamic.HeapWellTyped header.function.context heap)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context heap arguments header.types)
    (represented : Arguments model mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    {stages : Staging.Recursive.Registry} {invocation child : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    (selected : stages.Closure header.function child)
    (budget : Nat)
    (children : NamedLiftsBelow (headers := headers) (keys := keys) header model stages child budget)
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size context callerEvidence function.evidence heap (.global function) arguments outcome after)
    (within : size ≤ budget) :
    ApplicationLift (Program.ofChecked compiled.sourceProgram) stages invocation context heap
      (.global function) arguments outcome after := by
  let authority := (caller.rows owner.position).authority
  have physical : authority.frameLocation = owner.key.frameLocation := (caller.rows owner.position).frame_eq
  change authority.frameLocation = keys[owner.position.val].frameLocation at physical
  have liveLocals : Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
    obtain ⟨original⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool caller owner member
    exact original.locals
  have liveReference : (physicalCapture.named).canonical[header.globals]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type authority.frameLocation) := by
    simpa only [physical, CallableIndexedOwnedFunctionValues.OwnedKey.key] using (physicalCapture.named).reference
  have arity : header.function.parameters.length = arguments.length := by
    rw [header.parameters, List.length_map]; exact represented.length.1
  obtain ⟨childSize, environment, bound, allocated, sourceTrace, smaller⟩ :=
    source_prefix sourceAt owners arity trace
  obtain ⟨finalContext, bodyOutcome, bodyTrace, converted⟩ := body_control sourceTrace
  obtain ⟨origin, index, metadata, owned, history, emitted⟩ :=
    CallableIndexedFormation.namedBody_history compiled.indexed.ancestry header.hook
  let installed := CallableIndexedOwnedFunctionState.install caller owner.position (.stable history)
  let installedAuthority := authority.install (.stable history)
  have installedHeaps := (CallableIndexedBodyFrames.install header.registered heaps authority.unmapped authority.typed
    authority.frame (.stable history)).1
  have layout : EnvironmentsAgree
      (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift))
      (DataPatternValues.packValues payloads :: (physicalCapture.named).canonical)
      (.unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured) :=
    GenericExpressionMeaning.agree_prefix
      (GenericExpressionMeaning.agree_prefix (ReadOnly.EnvironmentsAgree.lift (physicalCapture.named).layout (DataPatternValues.packValues payloads))
        (encode compiled.indexed.ancestry.layout.frame authority.current)) .unit
  have packTyped : RuntimeValueHasType world (DataPatternValues.packValues payloads)
      header.named.signature.parameterType (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions :=
    header.parameterType.symm ▸ CallableIndexedParameters.Arguments.pack_typed represented
  have actualTyped := RuntimeEnvironmentHasTypes.cons
    (RuntimeValueHasType.unit (definitions := (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions))
    (.cons (encode_runtime_typed world header.registered authority.current) (.cons packTyped (physicalCapture.named).typed))
  let producer : ProtectedStateTransition.MarkedAllocation.Producer (protocol headers keys)
      header.layouts compiled.indexed.ancestry.layout.frame model :=
    sameLayouts.symm ▸ CallableIndexedOwnedMarkedAllocation.producer headers keys model
  have readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary authority.frameLocation (.state index) := by
    exact readyAt_cast sameLayouts _ (CallableIndexedOwnedAllocationProducer.readyAt_of_owner_eq
      model owner.position physical.symm history)
  let parameterInitial : State headers keys
      ⟨[], mapping, world, heap, store.set authority.frameLocation (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩ :=
    Eq.mp (congrArg (fun location => State headers keys
      ⟨[], mapping, world, heap, store.set location (encode compiled.indexed.ancestry.layout.frame (.state index)), (physicalCapture.named).canonical⟩)
      physical.symm) installed
  obtain ⟨entry, parameterTransition, agreement, spine⟩ :=
    CallableIndexedOwnedPreparedStagedPhysicalNamedEntryBounds.parameters_with_state_spine installedAuthority
    (physicalCapture.named).environments liveLocals liveReference (physicalCapture.named).coherent represented installedHeaps
    layout actualTyped producer parameterInitial readyAt
  obtain ⟨parameterState, parameterRelated⟩ := parameterTransition
  obtain ⟨sameEnvironment, sameHeap⟩ := FunctionCallBody.allocations_same entry.allocation allocated
  rw [← sameEnvironment, ← sameHeap] at bodyTrace
  have installedRelated : Relates caller parameterInitial := by
    exact related_cast_frame caller physical.symm installed
      (CallableIndexedOwnedFunctionState.install_related caller owner.position (.stable history))
  let receipt : CallableIndexedOwnedPreparedNamedParameterReceipts.Receipt (registry := registry) functions owner caller header arguments :=
    ⟨origin, index, metadata, (physicalCapture.named).administrative, _,
      .unit :: encode compiled.indexed.ancestry.layout.frame authority.current :: DataPatternValues.packValues payloads :: (physicalCapture.named).captured,
      Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) (physicalCapture.named).embedding.lift),
      authority.frameLocation, (caller.rows owner.position).frame_eq, owned, history, emitted,
      entry, parameterState, installedRelated.trans parameterRelated, stable, heapTyped, argumentsTyped⟩
  have admitted : Admission poolBridge header.context parameterState := ⟨(SelectedCompilationNamedAdmission.parameter_source certified receipt.body.allocation receipt.heapTyped receipt.argumentsTyped).heapTyped, receipt.rows⟩
  have physicalEntry := (physicalAuthority.install authority.frame.read (.state index)).extend entry.frame
  have physicalSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 1
      (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.canonical := by
    obtain ⟨added, length, same⟩ := spine
    intro slot signature found
    rw [same]
    have offset : (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))).length + 1 + slot =
        added.length + (slot + 1) := by simp only [List.length_map, List.length_reverse]; omega
    rw [offset, List.getElem?_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left, List.getElem?_cons_succ, List.length_nil, Nat.zero_add] using physicalCapture.slots slot signature found
  have lifted := children entry.environments entry.heaps entry.locals entry.lookups
    entry.actualTyped parameterState admitted owner
    (fun zero globals => receipt.packet zero globals)
    physicalCapture.keyPhysical physicalEntry physicalSlots
    (by simpa only [stages.source selected, stages.evidence selected] using bodyTrace)
    (Nat.le_of_lt (Nat.lt_of_lt_of_le smaller within))
  have selectedActual : stages.Closure
      (Staging.Recursive.globalView header.sourceBody function.evidence header.function.body) child := by
    simpa only [CallableIndexedOwnedPreparedStagedNamedSourceScopeReceipts.global_view sourceAt] using selected
  have parameters : MonoBindersExtend header.sourceBody.source.owner header.sourceBody.context
      header.sourceBody.source.inputs header.types header.context := by
    simpa only [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] using header.extended
  exact SelectedCompilationStageBodyLiftBounds.BodyLift.global sourceAt.frame.instantiated
    (sourceAt.dictionary ▸ sourceAt.frame.covers) sourceAt.frame.roots selectedActual parameters
    (sourceAt.frame.parameters ▸ entry.allocation) lifted (sourceAt.frame.result ▸ converted)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageNamedInvocationLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
/-! Ordinary trace bounds for lifting selected expressions. The preconditions
are the actual physical caller state used by the closed staged preservation
family. A constructed child trace can therefore supply the reached state for
the next ordinary child, including its retained callable origins. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open SelectedCompilationMixedRootSupport (RootAt)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

section Bound
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (registry : Staging.Recursive.Registry) (invocation : Staging.Recursive.Scope)
  (certificate : GenericExpressionMeaning.Certificate)

def LiftsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual → RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    Admission bridge context initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context invocation.evidence invocation.source
      environment before id outcome after →
    ExpressionLift program registry invocation context environment before id outcome after
end Bound

section Roots
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  (stages : Staging.Recursive.Registry) (semanticFaults : FunctionCalls.FaultRep)

def LiftsRootsAt (size : Nat) : Prop :=
  ∀ {context invocation scope expression lowered}
    (root : RootAt compiled headers stages context invocation scope expression lowered semanticFaults)
    (owner : OwnedKey keys),
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers →
    LiftsAt
      (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys)
        root.compilation.administrativePrefix).forgetSlots
      context model stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope expression lowered) size
end Roots

section ActualPreservation
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {initial receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (support : SelectedCompilationPhysicalProgramSupport.Support compiled headers keys initial)
  (issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
    receiving.result.context.registry receiving.result.extension receiving.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry)

include issued extension in
/-- The already closed physical proof supplies reached states for constructed
staged prefixes. Its input is a finite trace, without an execution callback. -/
theorem preserves_roots (size : Nat) :
    SelectedCompilationMixedRootBounds.PreservesRootsAt (headers := headers) (keys := keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving.result.context.registry
        (SelectedCompilationPhysicalProgramSupport.functions support))
      (SelectedCompilationPhysicalProgramSupport.stages compiled)
      (CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults receiving.result.diagnostics) size := by
  exact SelectedCompilationPhysicalMixedCallerFamily.preserves_with_methods
    issued (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
    support.profile support.bodyTyping support.certificates
    (SelectedCompilationPhysicalProgramSupport.observations support)
    (SelectedCompilationPhysicalProgramSupport.static_extension support extension)
    (SelectedCompilationPhysicalProgramSupport.semantic_extension support issued extension)
    support.bodies support.bodySupport support.closurePackets support.closureSupport
    support.owners support.methods size
end ActualPreservation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
/-! Lift ordered ordinary arguments at their actual intervening states.
A completed staged child is passed through the closed preservation family
before the next child is lifted. A rejection keeps that child's exact prefix
heap and does not require an argument-tail execution. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open DataExpressionSequence
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open CallableIndexedOwnedSourceAdmission (Admission)
open SelectedCompilationStageLiftBounds (LiftsAt)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

def embedValues (outcome : DataExpressionSequence.Outcome) : Staging.Recursive.ValuesOutcome :=
  match outcome with
  | .ok values => .values values
  | .error reason => .fault (.semantic reason)

inductive ValuesAdapted (plain : DataExpressionSequence.Outcome) (plainAfter : Dynamic.Heap) :
    Staging.Recursive.ValuesOutcome → Dynamic.Heap → Prop where
  | completed : ValuesAdapted plain plainAfter (embedValues plain) plainAfter
  | rejected (origin : Staging.Recursive.Scope) (call : ExpressionId) (reason : Staging.CallGuard.Fault)
      (reached : Dynamic.Heap) :
      ValuesAdapted plain plainAfter (.fault (.stage origin call reason)) reached

def SequenceLift (program : Program) (registry : Staging.Recursive.Registry)
    (invocation : Staging.Recursive.Scope) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) (ids : List ExpressionId)
    (plain : DataExpressionSequence.Outcome) (plainAfter : Dynamic.Heap) : Prop :=
  ∃ staged reached,
    Staging.Recursive.Expressions program registry invocation context environment before ids staged reached ∧
    ValuesAdapted plain plainAfter staged reached

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {certificate : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep}

private def MemberTyping (ids : List ExpressionId) : Prop :=
  ∀ id, id ∈ ids → ∀ node, invocation.source.lookupExpression? id = some node →
    ExpressionHasType invocation.source context id node.type

private theorem values_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ sources after with
  | nil =>
    cases execution
    exact ⟨_, _, .nil, .completed⟩
  | single found generated =>
    cases execution with
    | cons head tail =>
      cases tail
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.value head)
      cases adapted with
      | completed => exact ⟨_, _, .cons trace .nil, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | cons head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
        cases restAdapted with
        | completed => exact ⟨_, _, .cons trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem values (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {sources : List Dynamic.Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsEvaluate program size context invocation.evidence
      invocation.source environment before ids sources after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.ok sources) after := by
  apply values_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

private theorem fault_members (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (sourceTyped : MemberTyping (context := context) (invocation := invocation) ids)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  induction tree generalizing size mapping world actual actualContext before store ξ reason after with
  | nil => cases execution
  | single found generated =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail _ failed => cases failed
  | @cons id node lowered next ids types nextCode codes found generated tail ih =>
    cases execution with
    | head failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found (sourceTyped _ (by simp) _ found) environments heaps locals layout actualTyped
        initial admitted (.fault failed)
      cases adapted with
      | completed => exact ⟨_, _, .headFault trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
    | tail head rest =>
      have typed := sourceTyped _ (by simp) _ found
      obtain ⟨staged, reached, trace, adapted⟩ := children _
        (Nat.lt_of_lt_of_le (SourceExecutionSize.child_lt_stepSize (by simp)) within)
        generated found typed environments heaps locals layout actualTyped initial admitted (.value head)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .headFault trace, .rejected origin call reason _⟩
      | completed =>
        obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
        obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
            maps, worlds, _frame, metadata, middleState, _related, post⟩ := preservation stagedSize
          generated found typed environments heaps locals layout actualTyped initial admitted measured
        obtain ⟨outcome, finalHeap, restTrace, restAdapted⟩ := ih
          (fun child member => sourceTyped child (List.mem_cons_of_mem _ member))
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 rest
          (Nat.le_trans (Nat.le_of_lt (SourceExecutionSize.child_lt_stepSize (by simp))) within)
        cases restAdapted with
        | completed => exact ⟨_, _, .tailFault trace restTrace, .completed⟩
        | rejected origin call reason reached =>
          exact ⟨_, _, .tailFault trace restTrace, .rejected origin call reason _⟩

theorem fault (budget : Nat)
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : Tree invocation.source certificate scope ids sourceTypes codes)
    (unique : NodeOccurrencesUnique invocation.source)
    (sourceTyped : ExpressionsHaveTypes invocation.source context ids sourceTypes)
    (children : ∀ size, size < budget → LiftsAt bridge context model registry invocation certificate size)
    (preservation : ∀ size, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation certificate faults size)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial) {size : Nat}
    (execution : SourceExecutionSize.ExpressionsFault program size context invocation.evidence
      invocation.source environment before ids reason after) (within : size ≤ budget) :
    SequenceLift program registry invocation context environment before ids (.error reason) after := by
  apply fault_members bridge budget tree _ children preservation environments heaps locals layout actualTyped
    initial admitted execution within
  intro id member node found
  exact CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique sourceTyped member found

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftSequence
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
/-! Genuine pre-body argument-count failures keep their ordinary result and
heap when lifted. Matching arity is reserved for the actual entry producer. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
open Frontend SourceInference Staging.Recursive.Lifting

variable {program : Program} {stages : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {caller invocation : Dynamic.EvidenceEnvironment}
  {before after : Dynamic.Heap} {arguments : List Dynamic.Value}
  {size : Nat} {outcome : Dynamic.ExpressionOutcome}

theorem closure_mismatch {function : Dynamic.Closure}
    (mismatch : function.parameters.length ≠ arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.closure function) arguments outcome after) :
    ApplicationLift program stages scope context before (.closure function) arguments outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | closure _ _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)
    | closureUnit _ _ _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity rejected => exact ⟨_, _, .closureArity rejected, .completed⟩
    | closureBody _ _ _ _ allocated _ => exact False.elim (mismatch allocated.length_eq)
    | closureControlEscape _ _ _ _ allocated _ _ => exact False.elim (mismatch allocated.length_eq)

theorem global_mismatch {function : Dynamic.GlobalFunction} {body : Dynamic.BodyInstance}
    {closure : Dynamic.Closure}
    (unique : (program.functions.map (fun definition => definition.body.owner)).Nodup)
    (frame : NamedCalls.SourceFrame program function.instantiation body closure)
    (mismatch : closure.parameters.length ≠ arguments.length)
    (trace : RecursiveNamedCallBounds.CallOutcome program size context caller invocation before
      (.global function) arguments outcome after) :
    ApplicationLift program stages scope context before (.global function) arguments outcome after := by
  have rawMismatch : body.source.inputs.length ≠ arguments.length := by
    simpa only [frame.parameters] using mismatch
  cases trace with
  | value evaluated =>
    cases evaluated with
    | global actual _ _ invoked =>
      cases BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases invoked with
      | returned _ _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)
      | unit _ _ _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | globalSignatureMissing missing =>
      cases frame.instantiated with
      | intro signatureMem _ declaration _ _ _ _ _ =>
        exact False.elim (missing _ signatureMem declaration.symm)
    | globalBodyMissing missing =>
      cases frame.instantiated with
      | intro _ definitionMem declaration owner _ _ _ _ =>
        exact False.elim (missing _ definitionMem (owner.trans declaration.symm))
    | globalArity actual rejected => exact ⟨_, _, .globalArity actual rejected, .completed⟩
    | globalBody actual _ failed =>
      cases BuiltinNamedCalls.instantiation_unique unique frame.instantiated actual
      cases failed with
      | arity rejected => exact ⟨_, _, .globalArity actual rejected, .completed⟩
      | statements _ _ allocated _ => exact False.elim (rawMismatch allocated.length_eq)
      | controlEscape _ _ allocated _ _ => exact False.elim (rawMismatch allocated.length_eq)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageApplicationArity
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
/-! Actual tuple and nominal-constructor traces lift through the original
ordered compiler argument tree. Successful values and semantic failures keep
their ordinary endpoint; a rejected child retains its exact reached heap. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

theorem tree_types {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {stored : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree source certificate scope ids stored codes)
    (unique : NodeOccurrencesUnique source) (typing : ExpressionsHaveTypes source context ids types) : stored = types := by
  induction tree generalizing types with
  | nil => cases typing; rfl
  | single found _generated =>
    cases typing with
    | cons head tail =>
      cases tail
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      exact congrArg (fun type => [type]) sourceType
  | cons found _generated tail ih =>
    cases typing with
    | cons head rest =>
      obtain ⟨actual, contains, sourceType⟩ := head.stored_type
      cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
      rw [sourceType, ih rest]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

theorem tuple (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .tuple ids) (unique : NodeOccurrencesUnique invocation.source)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨actualTypes, typing, _sourceType⟩ := CompatibleExpressionTuples.source_types
    unique metadata.found form metadata.coercions typed
  cases tree_types sequence unique typing
  have occurrence : Staging.Recursive.Occurrence invocation expression (.tuple ids) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  obtain ⟨childSize, sourceOutcome, childTrace, packed, smaller⟩ :=
    CompatibleExpressionTuples.source_inv_at metadata form unique execution
  cases packed with
  | values pack =>
    cases childTrace with
    | values evaluated =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted evaluated (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .tupleValue occurrence trace pack, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .tupleFault occurrence trace, .rejected origin call reason _⟩
  | fault reason =>
    cases childTrace with
    | fault failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted failed (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .tupleFault occurrence trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .tupleFault occurrence trace, .rejected origin call reason _⟩

theorem constructor (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId}
    {instantiation : DataConstructorInstantiation} {codes : List SourceCoreBasic.LoweredExpr}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .constructor instantiation ids) (unique : NodeOccurrencesUnique invocation.source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids instantiation.payloadTypes codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨_admissible, typing, _sourceType⟩ := CompatibleExpressionConstructors.constructor_source_types
    unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation expression (.constructor instantiation ids) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  obtain ⟨childSize, sourceOutcome, childTrace, packed, smaller⟩ :=
    RecursiveNamedDataExpressionSourceBounds.constructor_inv metadata form unique valid execution
  cases packed with
  | values sources =>
    cases childTrace with
    | values evaluated =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted evaluated (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .constructorValue occurrence valid trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .constructorFault occurrence trace, .rejected origin call reason _⟩
  | fault reason =>
    cases childTrace with
    | fault failed =>
      obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
        size sequence unique typing childLift preservation environments heaps locals layout actualTyped
        initial admitted failed (Nat.le_of_lt smaller)
      cases adapted with
      | completed => exact ⟨_, _, .constructorFault occurrence trace, .completed⟩
      | rejected origin call reason reached =>
        exact ⟨_, _, .constructorFault occurrence trace, .rejected origin call reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConstructors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
/-! Builtin applications have no nested body. Actual argument evaluation keeps
its original order, including a stage rejection in an argument prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

theorem builtin_application
    {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {callerEvidence invocationEvidence : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {function : Dynamic.BuiltinFunction}
    {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (applied : FunctionCallBody.Outcome program context callerEvidence invocationEvidence
      before (.builtin function) arguments outcome after) :
    Staging.Recursive.Applies program registry scope context before (.builtin function)
      arguments (embed outcome) after := by
  cases applied with
  | value applied =>
    cases applied with
    | builtin primitive => exact .builtin primitive
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | builtinArity mismatch => exact .builtinArity mismatch
    | builtinArgumentType arity mismatch => exact .builtinType arity mismatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}


theorem builtin (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {node : ExpressionNode}
    {lowered : SourceCoreBasic.LoweredExpr} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr} {function : BuiltinFunctionId}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .call callee ids (.builtinFunction function))
    (unique : NodeOccurrencesUnique invocation.source)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids types codes)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨actualTypes, typing⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  rw [form] at typing
  change ExpressionsHaveTypes invocation.source context ids actualTypes at typing
  cases SelectedCompilationStageLiftConstructors.tree_types sequence unique typing
  have occurrence : Staging.Recursive.Occurrence invocation expression (.call callee ids (.builtinFunction function)) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedBuiltinCallBounds.source_inv metadata form unique execution with
  | argumentsFault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted failed (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .builtinArgumentsFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .builtinArgumentsFault occurrence trace, .rejected origin call reason _⟩
  | apply evaluated applied smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted evaluated (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .builtinApplied occurrence trace (builtin_application applied), .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .builtinArgumentsFault occurrence trace, .rejected origin call reason _⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftBuiltin
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
/-! A direct declaration call lifts its exact ordered arguments and retained
named invocation. The physical caller frame supplies the original capture. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedDirectCallAuthority (Port EvidenceAt)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id callee ids instantiation reasonAt lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (idsUnique : RequirementIdsUnique context)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults idsUnique unique owners certified runtime in
theorem direct {children : GenericExpressionMeaning.Certificate}
    {child : Staging.Recursive.Scope} (selected : stages.Closure port.header.function child)
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodyLift : NamedLiftsBelow (headers := headers) (keys := keys) port.header model stages child size) :
    LiftsAt bridge context model stages invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨sourceTypes, calleeValid, _application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique receipt.metadata.found
      receipt.form receipt.metadata.coercions typed
  cases SelectedCompilationStageLiftConstructors.tree_types sequence unique typing
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedDirectArgumentRows.callee_receipt receipt runtime calleeValid
  obtain ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ := calleeOccurrence
  have calleeFound := lookupExpression?_complete unique calleeContains
  have calleeOccurrence : Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) :=
    ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩
  have occurrence : Staging.Recursive.Occurrence invocation expression
      (.call callee ids (.declaration instantiation)) receipt.node.requirements :=
    ⟨receipt.node, lookupExpression?_sound receipt.metadata.found, receipt.form, rfl, receipt.metadata.coercions⟩
  cases RecursiveNamedArgumentTraceBounds.source_inv_with_evidence receipt.metadata.found receipt.metadata.coercions
    receipt.form calleeFound evidenceAt.produces idsUnique unique execution with
  | argumentFault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted failed (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .rejected origin call reason _⟩
  | apply evaluated called argumentsSmaller callSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted evaluated (Nat.le_of_lt argumentsSmaller)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .directArgumentsFault occurrence calleeOccurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stageSize, sized⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨values, middleStore, middleMap, middleWorld, _argumentsEvaluated, represented, middleHeaps,
          _argumentMaps, _argumentWorlds, _argumentFrame, _argumentMetadata, reached, _related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge stageSize sequence unique typing
          (fun size _ => preservation size) environments heaps locals layout actualTyped initial admitted sized (Nat.le_refl _)
      obtain ⟨parameters, headerHeap, headerArguments, _supports⟩ :=
        SelectedCompilationDirectArgumentRows.at_successful_arguments receipt port
          certified runtime post.at_values.heap post.values_typed represented
      have sourceEq := CallableIndexedOwnedPreparedStagedDirectArgumentRows.global_eq receipt port evidenceAt evidenceAt.produces
      rw [sourceEq] at called
      obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
        port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
      obtain ⟨staged, finalHeap, applied, adapted⟩ :=
        SelectedCompilationStageNamedInvocationLifting.lifts_invocation functions owner (callerBridge.pool reached)
          port.header capture port.sourceAt port.aligned.layouts (physical reached) port.member owners certified
          post.at_values.rows headerHeap headerArguments parameters middleHeaps selected size bodyLift called (Nat.le_of_lt callSmaller)
      rw [← sourceEq] at applied
      exact ⟨staged, finalHeap, .directApplied occurrence calleeOccurrence valid trace evidenceAt.produces applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageDirectLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open CallablePreparedOperatorSourceBounds
open CallableIndexedOwnedPreparedStagedMethodSourceArguments (unary_dispatch binary_dispatch)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)


private theorem owned_eq {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout receipt.node.requirements receipt.node.coercions owned) :
    owned = receipt.node.requirements := by
  simpa only [Dynamic.OrdinaryRequirementLayout, receipt.metadata.coercions, coercionRequirementIds, List.flatMap_nil, List.append_nil] using layout.symm

include port in
private theorem requirement_safe
    (unique : RequirementIdsUnique context)
    {failed : RequirementId}
    (fault : Dynamic.RequirementListFaults context invocation.evidence receipt.node.requirements failed) : False := by
  have selected := port.selected
  generalize idsEq : receipt.node.requirements = ids at selected fault
  cases selected with
  | intro primary _ _ _ _ _ _ _ _ _ remaining _ _ _ =>
    cases primary with
    | intro produced _ =>
      cases fault with
      | head unavailable =>
        exact CallableCoercionRequirementSafety.excludes_unavailable
          (fun _ _ => unique.contains_unique) produced unavailable
      | tail _ failed =>
        exact CallableCoercionRequirementSafety.excludes_list_fault
          (fun _ _ _ _ => unique.contains_unique) remaining failed

private theorem raw_inv {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : RequirementIdsUnique context)
    (raw : RawOutcomeAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
      invocation.source environment before receipt.node outcome after) :
    RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence port.principal.dictionary
      invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
  have nonempty := CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected
  cases requirementsEq : receipt.node.requirements with
  | nil => exact False.elim (nonempty requirementsEq)
  | cons primary remaining =>
    rcases receipt.operator.form with ⟨operator, operand, form, arguments⟩ | ⟨operator, left, right, form, arguments⟩
    · have dispatch := unary_dispatch receipt port form
      rw [Receipt.arguments, arguments]
      cases outcome with
      | value value =>
        change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | unary layout operandEvaluated applied =>
          rw [owned_eq receipt layout, requirementsEq] at applied
          cases applied with
          | method actualDispatch actual invoked =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons operandEvaluated ?_ .nil) (.value invoked) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | fault reason =>
        change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | unaryOperand _ failed =>
          refine .argumentFault (.head failed ?_)
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | unaryApply layout operandEvaluated failed =>
          rw [owned_eq receipt layout, requirementsEq] at failed
          cases failed with
          | requirement fault => exact False.elim (requirement_safe receipt port unique (requirementsEq.symm ▸ fault))
          | method actualDispatch actual failed =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := unary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons operandEvaluated ?_ .nil) (.fault failed) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
    · have dispatch := binary_dispatch receipt port form
      rw [Receipt.arguments, arguments]
      cases outcome with
      | value value =>
        change SourceExecutionSize.ExpressionFormEvaluates _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | binaryShortCircuit layout _ _ empty =>
          exact False.elim (CallableIndexedOwnedPreparedStagedMethodSourceInversion.requirements_nonempty port.selected ((owned_eq receipt layout).symm.trans empty))
        | binaryEvaluateRight layout leftEvaluated _ rightEvaluated applied =>
          rw [owned_eq receipt layout, requirementsEq] at applied
          cases applied with
          | method actualDispatch actual invoked =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.value invoked) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
      | fault reason =>
        change SourceExecutionSize.ExpressionFormFaults _ _ _ _ _ _ _ _ _ _ _ _ at raw
        rw [form] at raw
        cases raw with
        | binaryLeft _ failed =>
          refine .argumentFault (.head failed ?_)
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | binaryLeftOperand _ _ invalid => exact False.elim (binary_dispatch_valid_left dispatch invalid)
        | binaryRight _ leftEvaluated _ failed =>
          refine .argumentFault (.tail leftEvaluated ?_ (.head failed ?_))
          all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)
        | binaryApply layout leftEvaluated _ rightEvaluated failed =>
          rw [owned_eq receipt layout, requirementsEq] at failed
          cases failed with
          | requirement fault => exact False.elim (requirement_safe receipt port unique (requirementsEq.symm ▸ fault))
          | method actualDispatch actual failed =>
            rw [← requirementsEq] at actual
            obtain ⟨sameTrait, sameMethod⟩ := binary_dispatch_unique dispatch actualDispatch
            cases sameTrait
            cases sameMethod
            obtain ⟨rfl, rfl⟩ := port.agrees _ _ actual
            refine .apply (.cons leftEvaluated ?_ (.cons rightEvaluated ?_ .nil)) (.fault failed) ?_
            all_goals (simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil]; omega)


/-- Every operand and selected body retains its original grade, strictly below
this whole ordinary expression. Empty compiler coercions remove only the empty
suffix; the actual selected body and complete dictionary remain unchanged. -/
theorem source_inv {size : Nat} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (requirements : RequirementIdsUnique context)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence invocation.source environment before id outcome after) :
    RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence port.principal.dictionary
      invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
  have notLocal : ∀ name binder, receipt.node.form ≠ .reference name (.local binder) := by
    intro name binder impossible
    rcases receipt.operator.form with ⟨_, _, form, _⟩ | ⟨_, _, _, form, _⟩ <;>
      rw [form] at impossible <;> cases impossible
  have weaken {small outcome after} (within : small ≤ size)
      (raw : RawTraceAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
        port.principal.dictionary invocation.source environment before receipt.arguments port.principal.sourceBody outcome after) :
      RawTraceAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
        port.principal.dictionary invocation.source environment before receipt.arguments port.principal.sourceBody outcome after := by
    have arguments {before ids values after}
        (trace : ArgumentsAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
          invocation.source environment before ids values after) :
        ArgumentsAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
          invocation.source environment before ids values after := by
      induction trace with
      | nil => exact .nil
      | cons head strict _ ih => exact .cons head (Nat.lt_of_lt_of_le strict within) ih
    have failed {before ids reason after}
        (trace : ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) small context invocation.evidence
          invocation.source environment before ids reason after) :
        ArgumentsFaultAt (Program.ofChecked compiled.sourceProgram) size context invocation.evidence
          invocation.source environment before ids reason after := by
      induction trace with
      | head failed strict => exact .head failed (Nat.lt_of_lt_of_le strict within)
      | tail head strict _ ih => exact .tail head (Nat.lt_of_lt_of_le strict within) ih
    cases raw with
    | argumentFault trace => exact .argumentFault (failed trace)
    | apply trace invoked strict => exact .apply (arguments trace) invoked (Nat.lt_of_lt_of_le strict within)
  cases raw_source_inv_sized receipt.metadata.found unique notLocal trace with
  | rawFault raw strict => exact weaken (Nat.le_of_lt strict) (raw_inv receipt port requirements raw)
  | path raw path rawStrict _ =>
    cases outcome with
    | value value =>
      change SourceExecutionSize.CoercionPathExecutes _ _ _ _ _ _ _ _ _ at path
      rw [receipt.metadata.coercions] at path
      cases path
      exact weaken (Nat.le_of_lt rawStrict) (raw_inv receipt port requirements raw)
    | fault reason =>
      change SourceExecutionSize.CoercionPathFaults _ _ _ _ _ _ _ _ _ at path
      rw [receipt.metadata.coercions] at path
      cases path

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProxyLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProxyLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {rawRegistry : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  (unique : NodeOccurrencesUnique invocation.source)

include unique in
/-- A proxy leaf preserves its independent ordinary result and exact heap.
Its original source form has no stage guard or child execution. -/
theorem lifts (size : Nat) :
    LiftsAt bridge context (CompatibleAmbientHeap.payloadModel values.checked rawRegistry functions)
      registry invocation (CompatibleExpressionProxies.Certificate values invocation.source) size := by
  intro scope id lowered certificate node found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | proxy receipt =>
    exact .completed (Staging.Recursive.Lifting.atomic_nonlocal unique
      (lookupExpression?_sound receipt.metadata.found)
      (by rw [receipt.form]; exact .proxy _)
      receipt.metadata.coercions (by intros; simp [receipt.form]) trace.sound)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageProxyLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedGroupBounds (Group)
universe u

theorem child_of_group {program : Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id inner : ExpressionId} {node : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .group inner) (empty : node.coercions = [])
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child, child < size ∧ RecursiveNamedCallBounds.ExpressionOutcome program child context evidence source environment before inner outcome after := by
  have sameNode : ∀ {other}, ContainsExpression source id other → other = node := by
    intro other contains
    exact Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro contains raw coercions =>
      cases sameNode contains
      rw [empty] at coercions
      cases coercions
      rw [form] at raw
      cases raw with
      | group _ child =>
        refine ⟨_, ?_, .value child⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
      cases sameNode contains
      rw [form] at otherForm
      cases otherForm
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found))
    | form contains raw =>
      cases sameNode contains
      rw [form] at raw
      cases raw with
      | group _ child =>
        refine ⟨_, ?_, .fault child⟩
        simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
    | coercion contains _ failed =>
      cases sameNode contains
      rw [empty] at failed
      cases failed
    | generalizedLocalRequirement contains otherForm _ _ _ _ _ _ _
    | generalizedLocalCoercion contains otherForm _ _ _ _ _ _ _ =>
      cases sameNode contains
      rw [form] at otherForm
      cases otherForm

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate}

theorem group (unique : NodeOccurrencesUnique invocation.source) (size : Nat)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model registry invocation children childSize) :
    LiftsAt bridge context model registry invocation (Group checked invocation.source children) size := by
  intro scope id lowered certificate actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  cases certificate with
  | actual metadata form innerFound sourceType child =>
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨innerNode, otherFound, _, innerTyped⟩ := CompatibleExpressionProducts.group_source_types
      unique metadata.found form metadata.coercions typed
    cases Option.some.inj (otherFound.symm.trans innerFound)
    obtain ⟨childSize, smaller, evaluated⟩ := child_of_group unique metadata.found form metadata.coercions trace
    obtain ⟨staged, reached, lifted, adapted⟩ := childLift childSize smaller child innerFound innerTyped
      environments heaps locals agrees actualTyped initial admitted evaluated
    exact ⟨staged, reached, .group ⟨_, lookupExpression?_sound metadata.found, form,
      metadata.requirements, metadata.coercions⟩ lifted, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageGroupLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)
universe u

private theorem literal_atomic {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

private theorem literal_coercions {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem literal_nonlocal {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    ∀ name binder, node.form ≠ .reference name (.local binder) := by
  cases literal with
  | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
  | resolvedWord form _ | resolvedInteger form _ => intros; simp [form]

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {rawRegistry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry rawRegistry)
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {readFuel : Nat} {reasonAt : ExpressionId → Word}
  {solved : List SolvedRequirement}
  (sameLedger : context.solvedRequirements = solved)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (unique : NodeOccurrencesUnique invocation.source)

local notation "valueModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked rawRegistry functions
local notation "trees" => Certificate readFuel
  (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
  invocation.source context solved reasonAt

include extension sameLedger runtimeLedger unique in
/-- Every leaf and pair prefix is reconstructed from the actual ordinary trace
and physical state. All results and semantic failures retain the exact heap. -/
theorem exact_trace {scope id lowered} (certificate : trees scope id lowered) :
    ∀ {node}, invocation.source.lookupExpression? id = some node →
      ExpressionHasType invocation.source context id node.type →
    ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext
        scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
      GenericHeap.HeapRepresents valueModel mapping world before store →
      Dynamic.EnvironmentAgrees before context.locals environment →
      EnvironmentsAgree ξ canonical actual →
      RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions →
    ∀ initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩,
      Admission bridge context initial →
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source environment before id outcome after →
      Staging.Recursive.Expression program registry invocation context environment before id (embed outcome) after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites with
  | literal _ receipt =>
    intro node found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    obtain ⟨actualNode, actualFound, literal, _⟩ := receipt
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound actualFound)
      (literal_atomic literal) (literal_coercions literal) (literal_nonlocal literal) trace
  | read receipt =>
    intro node found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    obtain ⟨certificate, _, binding⟩ := receipt
    obtain ⟨location, cell, lookup, read, _, _⟩ := locals.lookup binding.declared
    obtain ⟨_, selected, _, _, _, selectedRead, _, cellRep⟩ :=
      GenericHeap.lookup_visible environments heaps lookup certificate.slot
    cases read.functional selectedRead
    exact Staging.Recursive.Lifting.atomic_read unique (lookupExpression?_sound certificate.metadata.found)
      certificate.form certificate.metadata.coercions lookup read cellRep.ordinary trace
  | @group id node inner innerNode lowered metadata form innerFound sourceType child childSites ih =>
    intro actualNode found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨otherNode, otherFound, _, childTyped⟩ := CompatibleExpressionProducts.group_source_types
      unique metadata.found form metadata.coercions typed
    cases Option.some.inj (otherFound.symm.trans innerFound)
    exact .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      (ih innerFound childTyped environments heaps locals agrees actualTyped initial admitted
        (CompatibleExpressionProducts.group_inv metadata form unique trace))
  | @pair id node left right leftNode rightNode first second metadata form leftFound rightFound sourceType
      leftTree rightTree leftSites rightSites leftIH rightIH =>
    intro actualNode found typed mapping world administrative environment canonical actual actualContext before store ξ outcome after
      environments heaps locals agrees actualTyped initial admitted trace
    cases Option.some.inj (found.symm.trans metadata.found)
    obtain ⟨firstNode, secondNode, firstFound, secondFound, _, leftTyped, rightTyped⟩ :=
      CompatibleExpressionProducts.pair_source_types unique metadata.found form metadata.coercions typed
    cases Option.some.inj (firstFound.symm.trans leftFound)
    cases Option.some.inj (secondFound.symm.trans rightFound)
    have occurrence : Staging.Recursive.Occurrence invocation id (.tuple [left, right]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    have tailLift : ∀ {a middle},
        Dynamic.ExpressionEvaluates program context invocation.evidence invocation.source environment before left a middle →
        ∀ {outcome after}, Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
          environment middle right outcome after →
        Staging.Recursive.Expression program registry invocation context environment before left (.value a) middle ∧
        Staging.Recursive.Expression program registry invocation context environment middle right (embed outcome) after := by
      intro a middle evaluated outcome after tail
      have lifted := leftIH leftFound leftTyped environments heaps locals agrees actualTyped initial admitted (.value evaluated)
      obtain ⟨size, measured⟩ := Staging.Recursive.Size.Expression.of_trace lifted
      obtain ⟨value, middleStore, middleMap, middleWorld, _, represented, middleHeaps,
        maps, worlds, _, metadata, reached, _, post⟩ :=
        SelectedCompilationReadProductBounds.preserves bridge functions extension sameLedger runtimeLedger
          (semanticFaults := fun _ _ => True) (fun _ _ => True) (by intros; trivial)
          (by intros; trivial) unique size ⟨leftTree, leftSites⟩ leftFound leftTyped
          environments heaps locals agrees actualTyped initial admitted measured
      cases represented with
      | value payload =>
        exact ⟨lifted, rightIH rightFound rightTyped (environments.extend maps worlds) middleHeaps
          (locals.mono metadata) agrees (actualTyped.weaken worlds) reached post.at_value.2 tail⟩
    obtain ⟨sequence, children, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    cases packed with
    | values pack =>
      cases children with
      | values children =>
        cases children with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            cases pack with
            | cons tail =>
              cases tail
              obtain ⟨leftLift, rightLift⟩ := tailLift first (.value second)
              exact .pair occurrence leftLift rightLift
    | fault reason =>
      cases children with
      | fault failed =>
        cases failed with
        | head head =>
          exact .pairLeftFault occurrence
            (leftIH leftFound leftTyped environments heaps locals agrees actualTyped initial admitted (.fault head))
        | tail head tail =>
          cases tail with
          | head failed =>
            obtain ⟨leftLift, rightLift⟩ := tailLift head (.fault failed)
            exact .pairRightFault occurrence leftLift rightLift
          | tail _ impossible => cases impossible

include extension sameLedger runtimeLedger unique in
theorem lifts (size : Nat) : LiftsAt bridge context valueModel registry invocation trees size := by
  intro scope id lowered certificate node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees actualTyped initial admitted trace
  exact .completed (exact_trace bridge functions extension sameLedger runtimeLedger unique certificate found typed
    environments heaps locals agrees actualTyped initial admitted trace.sound)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageReadProductLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndexLifting
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndexLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open SelectedCompilationStageLiftBounds Staging.Recursive.Lifting
open CompatibleExpressionIndices
open CallableIndexedOwnedPreparedStagedIndexHeadBounds (Point)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {context : SourceSemantics.Context}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {children : GenericExpressionMeaning.Certificate} {faults : RecursiveStageMeaning.FaultRep}
  {values : SourceCoreCompatibleValues.Context}
  {scope : SourceCoreLocalCell.Scope} {id base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
  {layout : Core.OrderedMapping.Layout} {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked}
  {first second : SourceCoreBasic.LoweredExpr} {reason : Word}
  (header : Header values invocation.source id base node baseNode layout comparison first second)
  (keyFound : invocation.source.lookupExpression? key = some keyNode)
  (form : node.form = .index base key)

local notation "headCode" => SourceCoreBasic.LoweredExpr.mk layout.valueType
  (SourceCoreCompatibleDataExpressions.index layout comparison.expression first.expression second.expression reason)

include header keyFound form in
/-- Actual base and key outcomes lift in order. Completed prefixes supply the
physical caller state for the next child; stage rejection keeps its real heap. -/
theorem index (unique : NodeOccurrencesUnique invocation.source)
    (firstChild : children scope base first) (secondChild : children scope key second)
    (size : Nat)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model registry invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults childSize) :
    LiftsAt bridge context model registry invocation (Point scope id headCode) size := by
  intro current child lowered point actualNode found typed
    mapping world administrative environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans header.metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique found typed
  have baseTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change base ∈ [base, key]; simp) header.baseMetadata.found
  have keyTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change key ∈ [base, key]; simp) keyFound
  have occurrence : Staging.Recursive.Occurrence invocation child (.index base key) :=
    ⟨_, lookupExpression?_sound header.metadata.found, form, header.metadata.requirements, header.metadata.coercions⟩
  rcases (RecursiveNamedDataExpressionSourceBounds.index_inv header.metadata form unique trace).split with
    ⟨reason, childSize, rfl, failed, smaller⟩ |
    ⟨baseValue, middle, baseSize, baseTrace, baseSmaller, rest⟩
  · obtain ⟨staged, reached, lifted, adapted⟩ := childLift childSize smaller firstChild header.baseMetadata.found baseTyped
      environments heaps locals agrees actualTyped initial admitted (.fault failed)
    cases adapted with
    | completed => exact .completed (.indexBaseFault occurrence lifted)
    | rejected origin call why reached => exact .rejected (.indexBaseFault occurrence lifted)
  · obtain ⟨staged, reached, liftedBase, adapted⟩ := childLift baseSize baseSmaller firstChild header.baseMetadata.found baseTyped
      environments heaps locals agrees actualTyped initial admitted (.value baseTrace)
    cases adapted with
    | rejected origin call why reached => exact .rejected (.indexBaseFault occurrence liftedBase)
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace liftedBase
      obtain ⟨_, middleStore, middleMap, middleWorld, _, _, middleHeaps,
        maps, worlds, _, metadata, reached, _, post⟩ := preservation stagedSize firstChild header.baseMetadata.found baseTyped
          environments heaps locals agrees actualTyped initial admitted measured
      rcases rest with ⟨reason, keySize, rfl, failed, keySmaller⟩ | ⟨keyValue, keySize, keyTrace, keySmaller, terminal⟩
      · obtain ⟨staged, finalHeap, liftedKey, adaptedKey⟩ := childLift keySize keySmaller secondChild keyFound keyTyped
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          reached post.at_value.2 (.fault failed)
        cases adaptedKey with
        | completed => exact .completed (.indexKeyFault occurrence liftedBase liftedKey)
        | rejected origin call why reached => exact .rejected (.indexKeyFault occurrence liftedBase liftedKey)
      · obtain ⟨staged, finalHeap, liftedKey, adaptedKey⟩ := childLift keySize keySmaller secondChild keyFound keyTyped
          (environments.extend maps worlds) middleHeaps (locals.mono metadata) agrees (actualTyped.weaken worlds)
          reached post.at_value.2 (.value keyTrace)
        cases adaptedKey with
        | rejected origin call why reached => exact .rejected (.indexKeyFault occurrence liftedBase liftedKey)
        | completed =>
          exact .completed (.indexResult occurrence liftedBase liftedKey
            (CallableIndexedOwnedPreparedStagedIndexOutcomes.of_terminal terminal))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageIndexLifting
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConditional
/-! Ordinary conditionals lift only the selected branch. The actual staged
condition supplies the physical state of that branch; a rejected condition
stops at its reached heap. Source Bool typing excludes the malformed ordinary
condition alternative using the genuine successful prefix receipt. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConditional
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

theorem conditional (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {lowered conditionCode thenCode elseCode : SourceCoreBasic.LoweredExpr}
    {condition thenId elseId : ExpressionId}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .conditional condition thenId elseId)
    (unique : NodeOccurrencesUnique invocation.source)
    (conditionNativeType : conditionCode.type = .bool)
    (conditionGenerated : children scope condition conditionCode)
    (thenGenerated : children scope thenId thenCode)
    (elseGenerated : children scope elseId elseCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound,
      _conditionType, _thenType, _elseType, conditionTyped, thenTyped, elseTyped⟩ :=
    CompatibleExpressionConditionals.conditional_source_types unique metadata.found form metadata.coercions typed
  have occurrence : Staging.Recursive.Occurrence invocation expression (.conditional condition thenId elseId) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.conditional_inv metadata form unique execution with
  | fault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted (.fault failed)
    cases adapted with
    | completed => exact ⟨_, _, .conditionalFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
  | @branch childSize branchSize flag middle outcome after conditionTrace branchTrace smaller branchSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted (.value conditionTrace)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted measured
      cases flag with
      | false =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller elseGenerated elseFound elseTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
      | true =>
        obtain ⟨result, finalHeap, branch, adapted⟩ := childLift _ branchSmaller thenGenerated thenFound thenTyped
          (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
          (actualTyped.weaken worlds) middleState post.at_value.2 branchTrace
        exact ⟨result, finalHeap, .conditional occurrence trace branch, adapted⟩
  | invalid child invalid _runtimeType smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller conditionGenerated conditionFound
      conditionTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .conditionalFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace trace
      obtain ⟨_value, _store, _mapping, _world, _evaluated, represented, _heaps,
          _maps, _worlds, _frame, _metadata, _state, _related, _post⟩ := preservation stagedSize
        conditionGenerated conditionFound conditionTyped environments heaps locals layout actualTyped initial admitted measured
      cases represented with
      | value payload =>
        rw [conditionNativeType] at payload
        obtain ⟨flag, sourceEq, _coreEq⟩ := CompatibleExpressionPrimitives.bool_fields payload
        cases sourceEq
        exact False.elim (invalid trivial)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftConditional
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators
/-! Primitive operators lift actual ordinary operands in evaluation order.
Short-circuiting retains its single evaluated operand. A second operand uses
the physical state recovered from the first completed staged prefix. -/

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedFunctionState (Records)
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CompatibleExpressionPrimitives (Metadata)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)} {keys : List (Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {context : SourceSemantics.Context} {registry : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope} {children : GenericExpressionMeaning.Certificate}
  {faults : RecursiveStageMeaning.FaultRep} {checked : SourceCoreCompatibleCatalog.Checked}

theorem unary (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id operand : ExpressionId} {node childNode : ExpressionNode}
    {lowered childCode : SourceCoreBasic.LoweredExpr} {operator : Syntax.UnaryOp}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique invocation.source)
    (childFound : invocation.source.lookupExpression? operand = some childNode)
    (generated : children scope operand childCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  have childTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change operand ∈ [operand]; simp) childFound
  have occurrence : Staging.Recursive.Occurrence invocation expression (.unary operator operand) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.unary_inv metadata form unique execution with
  | value child applied smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .unary occurrence trace applied, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
  | fault child smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.fault child)
    cases adapted with
    | completed => exact ⟨_, _, .unaryOperandFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
  | invalid child failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller generated childFound
      childTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .unaryOperandFault occurrence trace, .rejected origin call reason _⟩
    | completed =>
      cases failed with
      | primitive invalid => exact ⟨_, _, .unaryInvalid occurrence trace invalid, .completed⟩
      | requirement failed => cases failed
      | method _ selected _ => cases selected

theorem binary (size : Nat)
    {scope : SourceCoreLocalCell.Scope} {id left right : ExpressionId}
    {node leftNode rightNode : ExpressionNode}
    {lowered leftCode rightCode : SourceCoreBasic.LoweredExpr} {operator : Syntax.BinaryOp}
    (metadata : Metadata checked invocation.source id node lowered.type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique invocation.source)
    (leftFound : invocation.source.lookupExpression? left = some leftNode)
    (rightFound : invocation.source.lookupExpression? right = some rightNode)
    (leftGenerated : children scope left leftCode) (rightGenerated : children scope right rightCode)
    (childLift : ∀ child, child < size → LiftsAt bridge context model registry invocation children child)
    (preservation : ∀ child, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model registry invocation children faults child) :
    LiftsAt bridge context model registry invocation (Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals layout actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans metadata.found)
  obtain ⟨types, operands⟩ := ProtectedStateExpressionOperandTyping.operand_types unique metadata.found typed
  have leftTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change left ∈ [left, right]; simp) leftFound
  have rightTyped := CallableIndexedOwnedAdmittedExpressionSequence.member_expression_typed unique operands
    (by rw [form]; change right ∈ [left, right]; simp) rightFound
  have occurrence : Staging.Recursive.Occurrence invocation expression (.binary left operator right) :=
    ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
  cases RecursiveNamedExpressionSourceBounds.binary_inv metadata form unique execution with
  | leftFault child smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.fault child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryLeftFault occurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | leftInvalid child invalid smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryLeftInvalid occurrence trace invalid, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | short child circuit smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := childLift _ smaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value child)
    cases adapted with
    | completed => exact ⟨_, _, .binaryShortCircuit occurrence trace circuit, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence trace, .rejected origin call reason _⟩
  | rightFault first continues second firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.fault second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed => exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .completed⟩
  | value first continues second applied firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.value second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed => exact ⟨_, _, .binary occurrence firstTrace continues secondTrace applied, .completed⟩
  | invalid first continues second failed firstSmaller secondSmaller =>
    obtain ⟨staged, reached, firstTrace, adapted⟩ := childLift _ firstSmaller leftGenerated leftFound
      leftTyped environments heaps locals layout actualTyped initial admitted (.value first)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .binaryLeftFault occurrence firstTrace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stagedSize, measured⟩ := Staging.Recursive.Size.Expression.of_trace firstTrace
      obtain ⟨_value, middleStore, middleMap, middleWorld, _evaluated, _represented, middleHeaps,
          maps, worlds, _frame, heapMetadata, middleState, _related, post⟩ := preservation stagedSize
        leftGenerated leftFound leftTyped environments heaps locals layout actualTyped initial admitted measured
      obtain ⟨result, finalHeap, secondTrace, adapted⟩ := childLift _ secondSmaller rightGenerated rightFound rightTyped
        (environments.extend maps worlds) middleHeaps (locals.mono heapMetadata) layout
        (actualTyped.weaken worlds) middleState post.at_value.2 (.value second)
      cases adapted with
      | rejected origin call reason reached =>
        exact ⟨_, _, .binaryRightFault occurrence firstTrace continues secondTrace, .rejected origin call reason _⟩
      | completed =>
        cases failed with
        | primitive invalid => exact ⟨_, _, .binaryInvalid occurrence firstTrace continues secondTrace invalid, .completed⟩
        | requirement failed => cases failed
        | method _ selected _ => cases selected

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageLiftOperators
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectSource
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectSource
open Frontend SourceInference
open SelectedCompilationStageCoercionLiftBounds

private def Available (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (ids : List RequirementId) : Prop :=
  ∀ id, id ∈ ids → ¬ Dynamic.RequirementUnavailable context evidence id

private theorem produced_available {context : Context} {evidence produced : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate}
    (unique : RequirementIdsUnique context)
    (receipt : Dynamic.RequirementsProduceEnvironment context evidence ids predicates produced) :
    Available context evidence ids := by
  induction receipt with
  | nil => intro id member; cases member
  | cons head tail ih =>
    intro id member
    rcases List.mem_cons.mp member with same | member
    · subst id; exact head.excludes_unavailable unique
    · exact ih id member

private theorem selected_available {program : Program} {context : Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
    {traitName methodName : String} {ids : List RequirementId} {body : Dynamic.BodyInstance}
    (unique : RequirementIdsUnique context)
    (selected : Dynamic.OperatorMethodSelected program context evidence traitName methodName ids body dictionary) :
    Available context evidence ids := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ methods _ _ _ =>
    cases selects with
    | intro primary _ =>
      intro id member
      rcases List.mem_cons.mp member with same | member
      · subst id; exact primary.excludes_unavailable unique
      · exact produced_available unique methods id member

private theorem chain_available {compiled : SourceCoreUnifiedCompilation.Compiled}
    {project compilation caller available scope node policy context invocation stages source target input steps output calls}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled project compilation caller available
      scope node policy context invocation stages source target input steps output calls)
    (unique : RequirementIdsUnique context) : Available context invocation.evidence (coercionRequirementIds steps) := by
  induction chain with
  | nil => intro id member; cases member
  | cons step port valid tail ih =>
    intro id member
    rcases List.mem_append.mp member with member | member
    · exact selected_available unique port.selected id member
    · exact ih id member

private theorem requirements_available {context : Context} {evidence dictionary : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {steps : List CoercionStep} {predicates : List ProgramPredicate}
    (unique : RequirementIdsUnique context)
    (produced : Dynamic.DirectCallProducesEvidence context evidence ids steps predicates dictionary)
    (coercions : Available context evidence (coercionRequirementIds steps)) : Available context evidence ids := by
  cases produced with
  | intro stepsEq idsEq produced =>
    subst steps
    subst ids
    rw [coercionRequirementIds_append] at coercions
    intro id member
    rcases List.mem_append.mp member with member | member
    · exact coercions id (List.mem_append_left _ member)
    · rcases List.mem_append.mp member with member | member
      · exact produced_available unique produced id member
      · exact coercions id (List.mem_append_right _ member)

private theorem available_excludes {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {ids : List RequirementId} {predicates : List ProgramPredicate} {failed : RequirementId}
    (available : Available context evidence ids)
    (fault : Dynamic.RequirementsFault context evidence ids predicates failed) : False := by
  induction fault with
  | head missing => exact available _ (by simp) missing
  | tail _ _ ih => exact ih (fun id member => available id (by simp [member]))

/-- The exact selected conversion ports and declaration dictionary cover the
whole retained requirement partition, including the conversion requirements. -/
theorem requirements_safe {compiled : SourceCoreUnifiedCompilation.Compiled}
    {project compilation caller available scope node policy context invocation stages source target input steps output calls}
    (chain : CallableIndexedOwnedPreparedStagedCoercionChain.Chain compiled project compilation caller available
      scope node policy context invocation stages source target input steps output calls)
    {ids : List RequirementId} {predicates : List ProgramPredicate} {dictionary : Dynamic.EvidenceEnvironment}
    (unique : RequirementIdsUnique context)
    (produced : Dynamic.DirectCallProducesEvidence context invocation.evidence ids steps predicates dictionary)
    {failed : RequirementId} (fault : Dynamic.RequirementsFault context invocation.evidence ids predicates failed) : False :=
  available_excludes (requirements_available unique produced (chain_available chain unique)) fault

/-- Raw declaration calls keep their original coercion partition while
exposing the actual ordered argument prefix and exact invocation dictionary. -/
theorem raw_call {program : Program} {context : Context} {source : TypedSource}
    {caller invocation : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {requirements : List RequirementId} {coercions : List CoercionStep}
    {calleeNode : ExpressionNode} {size : Nat} {outcome : Dynamic.ExpressionOutcome}
    (found : source.lookupExpression? callee = some calleeNode)
    (agrees : ∀ dictionary, Dynamic.DirectCallProducesEvidence context caller requirements coercions
      instantiation.predicates dictionary → dictionary = invocation)
    (safe : ∀ failed, ¬ Dynamic.RequirementsFault context caller requirements instantiation.predicates failed)
    (trace : RawOutcome program size context caller source environment before
      (.call callee ids (.declaration instantiation)) requirements coercions outcome after) :
    RecursiveNamedArgumentTraceBounds.TraceAt program context caller invocation source environment before
      ids instantiation size outcome after := by
  cases trace with
  | value evaluated =>
    cases evaluated with
    | directCall _ _ _ _ _ arguments produced applied =>
      have same := agrees _ produced
      subst same
      exact .apply arguments (.value applied) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))
  | fault failed =>
    cases failed with
    | directCalleeMissing missing => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains missing (lookupExpression?_sound found))
    | directArguments _ _ failed => exact .argumentFault failed (SourceExecutionSize.child_lt_stepSize (by simp))
    | directRequirements _ fault => exact False.elim (safe _ fault)
    | directApply arguments produced failed =>
      have same := agrees _ produced
      subst same
      exact .apply arguments (.fault failed) (SourceExecutionSize.child_lt_stepSize (by simp))
        (SourceExecutionSize.child_lt_stepSize (by simp))

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectSource
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectLifting
/-! A direct declaration call lifts its exact ordered arguments and retained
named invocation. The physical caller frame supplies the original capture. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedRawDirectAuthority (Port EvidenceAt)
open SelectedCompilationStageCoercionLiftBounds
open SelectedCompilationStageLiftBounds (LiftsAt)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open SelectedCompilationStageBodyLiftBounds (NamedLiftsBelow)
open Staging.Recursive.Lifting (ExpressionLift Adapted embed)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {project : SourceCoreEvidence.Projector} {caller : SourceSpecialization.SpecializedFunction}
  {lowerChild : SourceCoreEvidence.Child} {fuel : Nat} {callables : SourceCoreFunctions.CallablePolicy}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
  (receipt : CallableCoercionExpressionCertificates.Direct compiled.sourceProgram project caller compilation
    lowerChild fuel invocation.source scope id callee ids instantiation reasonAt callables node lowered)
  (port : Port receipt headers)
  (evidenceAt : EvidenceAt receipt port context invocation.evidence)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (keyPhysical : CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (owners : ((Program.ofChecked compiled.sourceProgram).functions.map (fun definition => definition.body.owner)).Nodup)
  (certified : SelectedCompilationNamedSourceTyping.Certified port.header)
  (shaped : SelectedCompilationSourceSignatureFacts.Shape port.header)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions


variable {stages : Staging.Recursive.Registry}

include owner receipt port evidenceAt callerBridge keyPhysical physical functions faults unique owners certified shaped runtime in
theorem raw_direct {children : GenericExpressionMeaning.Certificate}
    {child : Staging.Recursive.Scope} (selected : stages.Closure port.header.function child)
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope ids
      (port.header.bindings.map (fun binding => binding.1.scheme.body)) receipt.loweredArguments)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodyLift : NamedLiftsBelow (headers := headers) (keys := keys) port.header model stages child size)
    (safe : ∀ failed, ¬ Dynamic.RequirementsFault context invocation.evidence node.requirements
      instantiation.predicates failed)
    (typed : ExpressionHasType invocation.source context id node.type)
    {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
      mapping world administrativeContext scope environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked receiving functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope,mapping,world,before,store,canonical⟩)
    (admitted : Admission bridge context initial)
    (execution : RawOutcome (Program.ofChecked compiled.sourceProgram) size context invocation.evidence invocation.source
      environment before node.form node.requirements node.coercions outcome after) :
    RawLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before
      node.form node.requirements node.coercions outcome after := by
  obtain ⟨sourceTypes, calleeValid, application, typing⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.source_types receipt unique typed
  have rows := SelectedCompilationRawDirectSourceTypes.source_types receipt port.toReady shaped runtime.signatures application
  have typing := rows.1 ▸ typing
  obtain ⟨name, calleeOccurrence, valid⟩ :=
    CallableIndexedOwnedPreparedStagedRawDirectArguments.callee_receipt receipt port runtime calleeValid
  obtain ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩ := calleeOccurrence
  have calleeFound := lookupExpression?_complete unique calleeContains
  have calleeOccurrence : Staging.Recursive.Occurrence invocation callee (.reference name (.declaration instantiation)) :=
    ⟨calleeNode, calleeContains, calleeForm, calleeRequirements, calleeCoercions⟩
  rw [receipt.form] at execution ⊢
  cases SelectedCompilationStageRawDirectSource.raw_call calleeFound evidenceAt.agrees safe execution with
  | argumentFault failed smaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.fault bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted failed (Nat.le_of_lt smaller)
    cases adapted with
    | completed => exact ⟨_, _, .rawDirectArgumentsFault calleeOccurrence trace, .completed⟩
    | rejected origin call reason reached =>
      exact ⟨_, _, .rawDirectArgumentsFault calleeOccurrence trace, .rejected origin call reason _⟩
  | apply evaluated called argumentsSmaller callSmaller =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageLiftSequence.values bridge
      size sequence unique typing childLift preservation environments heaps locals layout actualTyped
      initial admitted evaluated (Nat.le_of_lt argumentsSmaller)
    cases adapted with
    | rejected origin call reason reached =>
      exact ⟨_, _, .rawDirectArgumentsFault calleeOccurrence trace, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨stageSize, sized⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨values, middleStore, middleMap, middleWorld, _argumentsEvaluated, represented, middleHeaps,
          _argumentMaps, _argumentWorlds, _argumentFrame, _argumentMetadata, reached, _related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge stageSize sequence unique typing
          (fun size _ => preservation size) environments heaps locals layout actualTyped initial admitted sized (Nat.le_refl _)
      obtain ⟨parameters, headerHeap, headerArguments, _supports⟩ :=
        SelectedCompilationRawDirectArgumentRows.at_successful_arguments receipt port
          certified runtime post.at_values.heap post.values_typed represented
      have sourceEq := CallableIndexedOwnedPreparedStagedRawDirectArguments.global_eq receipt port evidenceAt evidenceAt.produces
      rw [sourceEq] at called
      obtain ⟨capture⟩ := CallableIndexedOwnedNamedPhysicalCaptures.of_headerAt
        port.prepared port.aligned port.member keyPhysical (physical reached) middleHeaps.runtime_hasTypes
      obtain ⟨staged, finalHeap, applied, adapted⟩ :=
        SelectedCompilationStageNamedInvocationLifting.lifts_invocation functions owner (callerBridge.pool reached)
          port.header capture port.sourceAt port.aligned.layouts (physical reached) port.member owners certified
          post.at_values.rows headerHeap headerArguments parameters middleHeaps selected size bodyLift called (Nat.le_of_lt callSmaller)
      rw [← sourceEq] at applied
      exact ⟨staged, finalHeap, .rawDirectApplied calleeOccurrence valid trace evidenceAt.produces applied, adapted⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageRawDirectLifting
end
