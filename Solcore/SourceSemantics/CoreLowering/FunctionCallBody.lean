import Solcore.SourceSemantics.CoreLowering.FunctionValues
import Solcore.SourceSemantics.CoreLowering.FunctionArguments
import Solcore.SourceSemantics.CoreLowering.GenericLexicalContext

/-! Ordinary closure invocation uses the independent source call rules. This
module factors their body outcomes and constructs the actual parameter prefix.
It assumes no body execution when authenticating code or allocating arguments.
The source heap metadata invariant remains separate from Core world typing. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.FunctionCallBody
open Core Frontend Frontend.SourceInference GeneralHeap CoreProof ReadOnly
open FunctionArguments

inductive Outcome (program : Program) (context : SourceSemantics.Context)
    (caller invocation : Dynamic.EvidenceEnvironment) (before : Dynamic.Heap)
    (function : Dynamic.Value) (arguments : List Dynamic.Value) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {result after} (execution : Dynamic.CallableApplies program context caller invocation before
      function arguments result after) : Outcome program context caller invocation before function arguments (.value result) after
  | fault {reason after} (execution : Dynamic.CallableFaults program context caller invocation before
      function arguments reason after) : Outcome program context caller invocation before function arguments (.fault reason) after

/-- These are precisely the body exits represented by the independent closure
call rules. Non-Unit fallthrough is not assigned an invented source fault. -/
inductive Trace (program : Program) (function : Dynamic.Closure) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | returned {finalContext result after}
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext (.returned result) after) :
      Trace program function context environment before (.value result) after
  | unit {finalContext finalEnvironment after}
      (resultUnit : function.resultType = .unit)
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext (.fallthrough finalEnvironment) after) :
      Trace program function context environment before (.value .unit) after
  | fault {finalContext reason after}
      (execution : Dynamic.FunctionStatementsFault program context function.evidence function.source
        environment before function.body finalContext reason after) :
      Trace program function context environment before (.fault reason) after
  | escaped {finalContext control after}
      (execution : Dynamic.FunctionStatementsExecute program context function.evidence function.source
        environment before function.body finalContext control after)
      (escape : (∃ environment, control = .breaking environment) ∨
        (∃ environment, control = .continuing environment)) :
      Trace program function context environment before (.fault .controlEscapedFunction) after

variable {program : Program} {function : Dynamic.Closure}

theorem Trace.call {context callContext : SourceSemantics.Context}
    {caller : Dynamic.EvidenceEnvironment} {before bound after : Dynamic.Heap}
    {arguments : List Dynamic.Value} {environment : Dynamic.Environment}
    {types : List TypeSystem.Ty} {outcome : Dynamic.ExpressionOutcome}
    (frame : Dynamic.ClosureFrame program function)
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types callContext)
    (allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound)
    (trace : Trace program function callContext environment bound outcome after) :
    Outcome program context caller function.evidence before (.closure function) arguments outcome after := by
  cases trace with
  | returned execution => exact .value (.closure rfl frame extension allocation execution rfl)
  | unit resultUnit execution => exact .value (.closureUnit rfl frame resultUnit extension allocation execution ⟨_, rfl⟩)
  | fault execution => exact .fault (.closureBody rfl frame extension allocation execution)
  | escaped execution escape => exact .fault (.closureControlEscape rfl frame extension allocation execution escape)

/-- A finite source closure call exposes a body trace after source-order
parameter allocation. The represented argument list rules out arity faults. -/
theorem Outcome.trace {context : SourceSemantics.Context} {caller : Dynamic.EvidenceEnvironment}
    {before after : Dynamic.Heap} {arguments : List Dynamic.Value} {outcome : Dynamic.ExpressionOutcome}
    (arity : function.parameters.length = arguments.length)
    (execution : Outcome program context caller function.evidence before (.closure function) arguments outcome after) :
    ∃ types callContext environment bound,
      MonoBindersExtend function.source.owner function.context function.parameters types callContext ∧
      Dynamic.BindersAllocate function.captured before function.parameters arguments environment bound ∧
      Trace program function callContext environment bound outcome after := by
  cases execution with
  | value execution =>
    cases execution with
    | closure _ _ extended allocated executed returned =>
      subst returned
      exact ⟨_, _, _, _, extended, allocated, .returned executed⟩
    | closureUnit _ _ resultUnit extended allocated executed fellThrough =>
      obtain ⟨_, rfl⟩ := fellThrough
      exact ⟨_, _, _, _, extended, allocated, .unit resultUnit executed⟩
  | fault execution =>
    cases execution with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact False.elim (mismatch arity)
    | closureBody _ _ extended allocated fault => exact ⟨_, _, _, _, extended, allocated, .fault fault⟩
    | closureControlEscape _ _ extended allocated executed escape =>
      exact ⟨_, _, _, _, extended, allocated, .escaped executed escape⟩

theorem mono_binders {owner : Resolved.DeclarationId} {context finalContext : SourceSemantics.Context}
    {parameters : List TypedBinder} {types : List TypeSystem.Ty}
    (extension : MonoBindersExtend owner context parameters types finalContext) :
    BindersExtend owner context parameters finalContext ∧
      (∀ binder, binder ∈ parameters → binder.scheme.quantified = []) := by
  induction extension with
  | nil => exact ⟨.nil _, by intro binder member; cases member⟩
  | cons scheme head tail ih =>
    refine ⟨.cons head ih.1, ?_⟩
    intro binder member
    rcases List.mem_cons.mp member with rfl | member
    · simp [scheme, TypeSystem.Scheme.mono]
    · exact ih.2 binder member

/-- Static body and parameter typing are recovered from independent code
validity. They are not inferred from Core typing or successful execution. -/
theorem frame_body (frame : Dynamic.ClosureFrame program function) :
    ∃ types context finalContext facts,
      MonoBindersExtend function.source.owner function.context function.parameters types context ∧
      StatementsHaveType function.source {returnType := function.resultType, loopDepth := 0}
        context function.body finalContext facts ∧ BodyCompletes function.resultType facts := by
  obtain ⟨id, node, _, form, _, typed⟩ := frame.code.occurrence
  rw [form] at typed
  generalize annotated : (TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType) = type at typed
  cases typed with
  | lambda _ extended body completes => exact ⟨_, _, _, _, extended, body, completes⟩

/-- Every independently valid parameter installation reaches the statically
certified lambda body context. -/
theorem frame_body_at (frame : Dynamic.ClosureFrame program function)
    {types : List TypeSystem.Ty} {context : SourceSemantics.Context}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context) :
    ∃ finalContext facts,
      StatementsHaveType function.source {returnType := function.resultType, loopDepth := 0}
        context function.body finalContext facts ∧ BodyCompletes function.resultType facts := by
  obtain ⟨otherTypes, otherContext, finalContext, facts, other, body, completes⟩ := frame_body frame
  have typesSame : otherTypes = types := other.bodyTypes_eq.symm.trans extension.bodyTypes_eq
  subst otherTypes
  have contextSame := other.functional extension
  subst otherContext
  exact ⟨finalContext, facts, body, completes⟩

private theorem parameters_scope {policy : SourceCoreFunctions.Policy} {source : TypedSource}
    {scope finalScope : SourceCoreLocalCell.Scope} {parameters : List TypedBinder}
    {lowered : List (TypedBinder × Ty)}
    (tree : FunctionCode.Parameters policy source scope parameters lowered finalScope) :
    lowered.foldl (fun scope binding => (binding.1.id, binding.2) :: scope) scope = finalScope := by
  induction tree with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- A body entry records the real administrative captures and temporary slots.
The continuation agreement is bidirectional and applies to arbitrary bodies,
including bodies that construct new closures. -/
structure Entry {catalog : SourceCoreDataCatalog.Catalog}
    (model : GenericHeap.PayloadModel catalog) {bodyCertificate : FunctionCode.BodyCertificate}
    {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {entryActual : Environment}
    (layout : FunctionCaptures.Layout catalog initialMap initialWorld scope function.captured entryActual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    (before : Dynamic.Heap) (initialStore : Store) (context : SourceSemantics.Context)
    (arguments : List Dynamic.Value) (values : List Value) where
  environment : Dynamic.Environment
  heap : Dynamic.Heap
  canonical : Environment
  actual : Environment
  store : Store
  mapping : LocationMap
  world : StoreTyping
  embedding : Renaming
  allocation : Dynamic.BindersAllocate function.captured before function.parameters arguments environment heap
  environments : DataHeap.EnvRepresents catalog mapping world layout.administrativeContext
    code.artifact.bodyScope environment canonical
  heaps : GenericHeap.HeapRepresents model mapping world heap store
  locals : Dynamic.EnvironmentAgrees heap context.locals environment
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before heap
  lookups : EnvironmentsAgree embedding canonical actual
  agreement : ContinuationAgreement (DataPatternValues.packValues values :: entryActual) initialStore
    (code.artifact.rawBody.rename layout.embedding.lift) actual store (code.artifact.bodyCode.rename embedding)

/-- Installing the real parameter prefix constructs all heap and lexical facts.
No source or Core evaluation of the body is a premise. -/
theorem entry_exists {catalog : SourceCoreDataCatalog.Catalog}
    {model : GenericHeap.PayloadModel catalog} {bodyCertificate : FunctionCode.BodyCertificate}
    {policy : SourceCoreFunctions.Policy} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (layout : FunctionCaptures.Layout catalog mapping world scope function.captured actual)
    (code : FunctionValues.Code catalog program bodyCertificate policy function scope layout.administrativeContext)
    {before : Dynamic.Heap} {store : Store} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {arguments : List Dynamic.Value} {values : List Value}
    (extension : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (represented : Arguments model mapping world code.artifact.loweredParameters arguments values)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured) :
    Nonempty (Entry model layout code before store context arguments values) := by
  obtain ⟨environment, heap, canonical, actual, finalStore, finalMap, finalWorld, embedding,
      allocation, environments, finalHeaps, maps, worlds, frame, lookups, agreement⟩ :=
    parameters_prefix represented (body := code.artifact.bodyCode) (outputType := code.artifact.resultCore)
      layout.represented heaps (EnvironmentsAgree.lift (mapping := layout.embedding) layout.lookups
        (DataPatternValues.packValues values))
  rw [code.artifact.parametersTree.binders] at allocation
  rw [parameters_scope code.artifact.parametersTree] at environments
  have mono := mono_binders extension
  exact ⟨⟨environment, heap, canonical, actual, finalStore, finalMap, finalWorld, embedding,
    allocation, environments, finalHeaps, GenericLexicalContext.binders_agree mono.1 mono.2 locals allocation,
    maps, worlds, frame, GenericLexicalContext.binders_metadata allocation, lookups, agreement⟩⟩

/-- Independent source parameter allocation is deterministic. -/
theorem allocations_same {environment leftEnv rightEnv : Dynamic.Environment}
    {before left right : Dynamic.Heap} {binders : List TypedBinder} {values : List Dynamic.Value}
    (first : Dynamic.BindersAllocate environment before binders values leftEnv left)
    (second : Dynamic.BindersAllocate environment before binders values rightEnv right) :
    leftEnv = rightEnv ∧ left = right := by
  induction first generalizing rightEnv right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons allocation rest ih =>
    cases second with
    | cons other rest' => cases allocation; cases other; exact ih rest'

end Solcore.SourceSemantics.CoreLowering.FunctionCallBody
