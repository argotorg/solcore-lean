import Solcore.Test.SourceCoreMixedImperativeSource

/-! Independent source steps expose the exact local cells and append order.
Closures capture by value: a generalized `let` copies the environment before
storing its descriptor, and each identity call copies the descriptor's
captures before allocating its parameter. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMixedImperative
open Solcore Core Frontend SourceInference SourceSemantics
open Tests.SourceCoreGeneralizedIdentity (IdentityShape)
open Tests.SourceCoreSelectedInterleavedLocal (CallShape)
open Tests.SourceSemanticsCaptureCopies

def StoredValue (binder : TypedBinder) (environment : Dynamic.Environment)
    (heap : Dynamic.Heap) (value : Dynamic.Value) : Prop :=
  ∃ location cell, Dynamic.Environment.LooksUp environment binder.id location ∧
    Dynamic.Heap.Reads heap location cell ∧ cell.generalized = none ∧ cell.value = some value

def StoredIdentity {source : TypedSource} (shape : IdentityShape source)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap) : Prop :=
  ∃ definitionContext captured location cell,
    Dynamic.Environment.LooksUp environment shape.binder.id location ∧
    Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = some (shape.descriptor definitionContext captured) ∧
    Dynamic.RuntimeContextFields definitionContext context

/-- Copying a captured environment only appends cells. -/
theorem HeapAppends.of_copies (source : TypedSource) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    HeapAppends heap (copies source environment heap).2 :=
  copies_appends source environment heap

theorem HeapAppends.of_environmentCopies {source : TypedSource} {environment copied : Dynamic.Environment}
    {before after : Dynamic.Heap} (copy : Dynamic.EnvironmentCopies source environment before copied after) :
    HeapAppends before after :=
  appends_of_copies copy

theorem StoredValue.mono {binder : TypedBinder} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {value : Dynamic.Value} (stored : StoredValue binder environment before value)
    (append : HeapAppends before after) : StoredValue binder environment after value := by
  rcases stored with ⟨location,cell,lookup,read,ordinary,contents⟩
  exact ⟨location,cell,lookup,append.read read,ordinary,contents⟩

theorem StoredValue.under {binder next : TypedBinder} {environment : Dynamic.Environment}
    {heap : Dynamic.Heap} {value : Dynamic.Value} (stored : StoredValue binder environment heap value)
    (location : Dynamic.Location) (different : next.id ≠ binder.id) :
    StoredValue binder ((next.id,location) :: environment) heap value := by
  rcases stored with ⟨found,cell,lookup,read,ordinary,contents⟩
  exact ⟨found,cell,.tail different lookup,read,ordinary,contents⟩

theorem StoredIdentity.mono {source : TypedSource} {shape : IdentityShape source}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} (stored : StoredIdentity shape context environment before)
    (append : HeapAppends before after) : StoredIdentity shape context environment after := by
  rcases stored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
  exact ⟨definitionContext,captured,location,cell,lookup,append.read read,descriptor,fields⟩

theorem StoredIdentity.under {source : TypedSource} {shape : IdentityShape source}
    {context final : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    (stored : StoredIdentity shape context environment heap) (next : TypedBinder)
    (location : Dynamic.Location) (different : next.id ≠ shape.binder.id)
    (extended : BinderExtends source.owner context next final) :
    StoredIdentity shape final ((next.id,location) :: environment) heap := by
  rcases stored with ⟨definitionContext,captured,found,cell,lookup,read,descriptor,fields⟩
  exact ⟨definitionContext,captured,found,cell,.tail different lookup,read,descriptor,
    fields.trans (.ofBinderExtends extended)⟩

theorem read_value {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {binder : TypedBinder} {type : TypeSystem.Ty}
    (read : Tests.SourceCoreNamedBranch.Read source binder type) {value : Dynamic.Value}
    (stored : StoredValue binder environment heap value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap read.node.id value heap := by
  rcases stored with ⟨location,cell,lookup,selected,ordinary,contents⟩
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound read.found)
  · rw [read.form]
    exact .local (by rw [read.requirements,read.coercions]; rfl) lookup selected ordinary contents
  · rw [read.coercions]; exact .nil

theorem boolean_value {program : SourceSemantics.Program} {source : TypedSource}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {value : Bool} (node : BooleanAt source value) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap node.node.id (.bool value) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound node.found)
  · rw [node.form]
    exact .builtinBoolean (by rw [node.requirements,node.coercions]; rfl)
  · rw [node.coercions]; exact .nil

theorem call_typed {source : TypedSource} {binder : TypedBinder} {argument : ExpressionId} {type result : TypeSystem.Ty}
    (call : CallShape source binder argument type) {context : SourceSemantics.Context}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionHasType source context call.node.id result) :
    ∃ calleeType argumentType, ExpressionHasType source context call.callee.node.id calleeType ∧
      ExpressionHasType source context argument argumentType := by
  cases typed with
  | intro contains raw _ _ _ _ =>
    cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans call.found)
    rw [call.form] at raw
    cases raw with
    | indirectCall callee arguments _ =>
      cases arguments with
      | cons argument _ => exact ⟨_,_,callee,argument⟩

theorem StoredIdentity.invoke {program : SourceSemantics.Program} {source : TypedSource}
    {shape : IdentityShape source} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before argumentsHeap : Dynamic.Heap}
    (stored : StoredIdentity shape context environment before)
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {argument : ExpressionId} {type result : TypeSystem.Ty} (call : CallShape source shape.binder argument type)
    (builtin : type = .word ∨ type = .bool)
    (typed : ExpressionHasType source context call.node.id result) {value : Dynamic.Value}
    (argumentTrace : Dynamic.ExpressionEvaluates program context evidence source environment before argument value argumentsHeap) :
    ∃ after, Dynamic.ExpressionEvaluates program context evidence source environment before call.node.id value after ∧
      HeapAppends argumentsHeap after := by
  obtain ⟨calleeType, argumentType, callee, argumentTyped⟩ := call_typed call state.runtime.graph.nodeOccurrencesUnique typed
  obtain ⟨node,contains,sameType⟩ := callee.stored_type
  have sameNode := Option.some.inj ((lookupExpression?_complete state.runtime.graph.nodeOccurrencesUnique contains).symm.trans call.callee.found)
  subst node
  have ground : TypeWellFormed context type := by
    rcases builtin with same | same
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .word⟩
    · rw [same]; exact ⟨callee.type_admissible.binders,.builtin .bool⟩
  rcases stored with ⟨definitionContext,captured,location,cell,lookup,read,descriptor,fields⟩
  have descriptorTyped := ((state.heapTyped cell read.member).generalized_inv descriptor).2
  have argumentKept := wellFormed.wholeLanguagePreservation.expression _ _ _ _ _ _ _ _ _
    state.runtime state.covers state.locals state.heapTyped argumentTyped argumentTrace
  have readable : Readable argumentsHeap captured :=
    (Readable.of_agrees descriptorTyped.captures).mono argumentKept.heap_extends
  have trace := shape.invoke_from_typed call captured environment evidence state.runtime
    (by simpa only [state.runtime.signatures] using wellFormed.signatures)
    state.covers state.locals state.heapTyped (sameType.symm ▸ callee) ground lookup read descriptor fields argumentTrace
    (copies_spec_applySubstitution [(shape.typeVariable, type)] source readable)
  exact ⟨_,trace,(HeapAppends.of_copies source captured argumentsHeap).trans ⟨_,rfl⟩⟩


def valueHeap (before : Dynamic.Heap) (binder : TypedBinder) (value : Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{type := binder.scheme.body, value := some value}]⟩

/-- The generalized `let` copies the environment, then stores the principal
descriptor over the copies. -/
def identityHeap {source : TypedSource} (shape : IdentityShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) : Dynamic.Heap :=
  ⟨(copies source environment before).2.cells ++
    [{type := shape.binder.scheme.body, value := none,
      generalized := some (shape.descriptor context (copies source environment before).1)}]⟩

/-- The descriptor's location, after the copies of the environment. -/
def identityLocation (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    Dynamic.Location :=
  ⟨(copies source environment before).2.cells.length⟩

theorem identityHeap_appends {source : TypedSource} (shape : IdentityShape source) (context : SourceSemantics.Context)
    (environment : Dynamic.Environment) (before : Dynamic.Heap) :
    HeapAppends before (identityHeap shape context environment before) :=
  (HeapAppends.of_copies source environment before).trans ⟨_,rfl⟩

theorem generalized_step {program : SourceSemantics.Program} {source : TypedSource}
    (shape : IdentityShape source) (site : StatementAt source (.letDecl shape.binder (some shape.lambda.id)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before : Dynamic.Heap}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((shape.binder.id,identityLocation source environment before) :: environment))
      (identityHeap shape context environment before) ∧
    SourceState program source final evidence ((shape.binder.id,identityLocation source environment before) :: environment)
      (identityHeap shape context environment before) ∧
    StoredIdentity shape final ((shape.binder.id,identityLocation source environment before) :: environment)
      (identityHeap shape context environment before) ∧
    BinderExtends source.owner context shape.binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitialized _ mono _ => rw [shape.scheme] at mono; cases mono
  | letInitializedGeneralized polymorphic _ _ _ extended =>
    have snapshot := copies_spec source (Readable.of_agrees state.locals)
    have allocation : Dynamic.Heap.AllocatesGeneralized (copies source environment before).2
        (shape.descriptor context (copies source environment before).1)
        (identityLocation source environment before) (identityHeap shape context environment before) := .append
    have trace := Dynamic.StatementExecutes.letInitializedGeneralized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq snapshot
      (shape.captures context (copies source environment before).1) polymorphic extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,
      ⟨context,(copies source environment before).1,_,_,.head,allocation.reads_new,rfl,.ofBinderExtends extended⟩,
      extended⟩

theorem ordinary_step {program : SourceSemantics.Program} {source : TypedSource}
    {binder : TypedBinder} {initializer : ExpressionId} (site : StatementAt source (.letDecl binder (some initializer)))
    {context final : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {environment : Dynamic.Environment} {before middle : Dynamic.Heap} {value : Dynamic.Value}
    (state : SourceState program source context evidence environment before) (wellFormed : ProgramWellFormed program)
    (mono : binder.scheme.quantified = []) {control : ControlContext} {facts : StatementFacts}
    (typed : StatementHasType source control context site.node.id final facts)
    (initializerTrace : Dynamic.ExpressionEvaluates program context evidence source environment before initializer value middle) :
    Dynamic.StatementExecutes program context evidence source environment before site.node.id final
      (.fallthrough ((binder.id,⟨middle.cells.length⟩) :: environment)) (valueHeap middle binder value) ∧
    SourceState program source final evidence ((binder.id,⟨middle.cells.length⟩) :: environment) (valueHeap middle binder value) ∧
    StoredValue binder ((binder.id,⟨middle.cells.length⟩) :: environment) (valueHeap middle binder value) value ∧
    BinderExtends source.owner context binder final := by
  have form := form_at state.runtime.graph.nodeOccurrencesUnique site.found typed
  rw [site.formEq] at form
  cases form with
  | letInitializedGeneralized impossible _ _ _ _ => exact (impossible mono).elim
  | letInitialized _ _ extended =>
    have allocation : Dynamic.Heap.Allocates middle binder.scheme.body (some value)
        ⟨middle.cells.length⟩ (valueHeap middle binder value) := .append
    have trace := Dynamic.StatementExecutes.letInitialized (program := program)
      (evidence := evidence) (lookupStatement?_sound site.found) site.formEq initializerTrace mono extended allocation
    exact ⟨trace,state.after_statement wellFormed typed trace,⟨_,_,.head,allocation.reads_new,rfl,rfl⟩,extended⟩

end Tests.SourceCoreMixedImperative
