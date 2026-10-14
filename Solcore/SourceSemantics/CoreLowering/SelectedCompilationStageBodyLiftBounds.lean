import Solcore.SourceSemantics.Staging.RecursiveLiftOutcomes
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodyPorts

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
    {before bound after : Dynamic.Heap} {function : Dynamic.Closure} {types : List TypeSystem.Ty}
    {environment : Dynamic.Environment} {arguments : List Dynamic.Value}
    {plain : Dynamic.ControlOutcome} {outcome : Dynamic.ExpressionOutcome}
    (selected : registry.Closure function child)
    (valid : Dynamic.ClosureFrame program function)
    (parameters : MonoBindersExtend function.source.owner function.context function.parameters types bodyContext)
    (allocate : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (lifted : BodyLift program registry true child bodyContext environment bound function.body plainFinal plain after)
    (exit : CompatibleNamedBody.Exit function.resultType plain outcome) :
    Lifting.ApplicationLift program registry caller context before (.closure function) arguments outcome after := by
  obtain ⟨finalContext, staged, reached, trace, adapted⟩ := lifted
  obtain ⟨result, converted, resultAdapted⟩ := adapted.exit exit
  exact ⟨result, reached, .closure selected valid parameters allocate trace converted, resultAdapted⟩

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
