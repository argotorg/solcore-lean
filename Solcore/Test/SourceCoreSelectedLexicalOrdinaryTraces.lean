import Solcore.Test.SourceCoreInitialLexicalFailureBodies
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicSourceCallOutcomes

/-! Ordinary executions of the existing lexical program are constructed from
its original source nodes and fresh allocations, before any public execution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Tests.SourceCoreSelectedLexicalOrdinaryTraces
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)
open RecursiveNamedPublicPhysicalSessionState (PlainValue PlainFault)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def appendWord (before : Dynamic.Heap) (value : Option Dynamic.Value) : Dynamic.Heap :=
  ⟨before.cells ++ [{ type := .word, value := value }]⟩

def nextLocation (before : Dynamic.Heap) : Dynamic.Location := ⟨before.cells.length⟩

theorem ActualHeader.identity_plain
    (actual : ActualHeader fixture observed.identityRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) (value : Core.Word) :
    PlainValue anchor actual.header invocation before [.word value] (.word value)
      (appendWord before (some (.word value))) := by
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  have allocated : Dynamic.Heap.Allocates before observed.identityShape.binder.scheme.body
      (some (.word value)) (nextLocation before) (appendWord before (some (.word value))) := by
    rw [observed.identityShape.binderScheme]
    exact .append
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [.word value]
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value))) := by
    rw [parameters]
    exact .cons allocated (.nil _ _)
  have read : Dynamic.ExpressionEvaluates (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      observed.identityShape.read.id (.word value) (appendWord before (some (.word value))) := by
    apply Dynamic.ExpressionEvaluates.intro
      (lookupExpression?_sound (actual.source.symm ▸ observed.identityShape.readFound))
    · rw [observed.identityShape.readForm]
      exact .local (by rw [observed.identityShape.readRequirements, observed.identityShape.readCoercions]; rfl)
        .head allocated.reads_new rfl rfl
    · rw [observed.identityShape.readCoercions]; exact .nil
  have executed : Dynamic.FunctionStatementsExecute (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source
      [(observed.identityShape.binder.id, nextLocation before)] (appendWord before (some (.word value)))
      actual.header.function.body actual.header.context (.returned (.word value))
      (appendWord before (some (.word value))) := by
    rw [actual.identity_statements]
    have found := lookupStatement?_sound (actual.source.symm ▸ observed.identityShape.statementFound)
    exact .singleton found (by rw [observed.identityShape.statementForm]; intro expression impossible; cases impossible)
      (.returnValue found observed.identityShape.statementForm read)
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.returned executed)
  cases body with
  | value invoked =>
    refine ⟨rawD, global, sourceAt, .global sourceAt.frame.instantiated rfl ?_ ?_⟩
    · exact sourceAt.dictionary ▸ sourceAt.frame.covers
    · exact sourceAt.dictionary ▸ invoked

private theorem failed_extension (actual : ActualHeader fixture observed.failedRow.row) :
    ∃ finalContext, BinderExtends actual.header.function.source.owner actual.header.context
      observed.failedShape.binder finalContext := by
  obtain ⟨facts, final, typed, roots, complete⟩ := actual.aligned.bodyTyped
  rw [actual.source, observed.failedShape.roots] at typed
  simp only [List.filterMap_cons, List.filterMap_nil] at typed
  have unique : NodeOccurrencesUnique observed.failedRow.row.function.typedBody := actual.source ▸ actual.header.unique
  cases typed with
  | cons head tail =>
    cases head with
    | letUninitialized contains form mono generalized extended type =>
      have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans observed.failedShape.declaredFound)
      cases same
      rw [observed.failedShape.declaredForm] at form
      cases (StatementForm.letDecl.inj form).1
      exact ⟨_, actual.source.symm ▸ extended⟩
    | _ =>
      have same := Option.some.inj ((lookupStatement?_complete unique (by assumption)).symm.trans observed.failedShape.declaredFound)
      cases same
      simp_all [observed.failedShape.declaredForm]

theorem ActualHeader.failed_plain
    (actual : ActualHeader fixture observed.failedRow.row)
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt actual.header rawD global)
    (anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram))
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap) :
    PlainFault anchor actual.header invocation before [] (.uninitializedLocation (nextLocation before))
      (appendWord before none) := by
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  have bound : Dynamic.BindersAllocate [] before actual.header.function.parameters [] [] before := by
    rw [parameters]; exact .nil _ _
  have allocated : Dynamic.Heap.Allocates before observed.failedShape.binder.scheme.body none
      (nextLocation before) (appendWord before none) := by
    rw [observed.failedShape.binderScheme]; exact .append
  obtain ⟨finalContext, extension⟩ := failed_extension actual
  have read : Dynamic.ExpressionFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      finalContext actual.header.function.evidence actual.header.function.source
      [(observed.failedShape.binder.id, nextLocation before)] (appendWord before none)
      observed.failedShape.read.id (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    apply Dynamic.ExpressionFaults.form
      (lookupExpression?_sound (actual.source.symm ▸ observed.failedShape.readFound))
    rw [observed.failedShape.readForm]
    apply Dynamic.ExpressionFormFaults.localUninitialized (owned := [])
      (cell := {type := observed.failedShape.binder.scheme.body, value := none})
      (by rw [observed.failedShape.readRequirements, observed.failedShape.readCoercions]; rfl)
      .head allocated.reads_new rfl rfl
    rw [observed.failedShape.binderScheme]
    intro ⟨key, value, impossible⟩
    cases impossible
  have executed : Dynamic.FunctionStatementsFault (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      actual.header.context actual.header.function.evidence actual.header.function.source [] before
      actual.header.function.body finalContext (.uninitializedLocation (nextLocation before)) (appendWord before none) := by
    rw [actual.failed_statements]
    exact .tail
      (.letUninitialized (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.declaredFound))
        observed.failedShape.declaredForm (by rw [observed.failedShape.binderScheme]; rfl) extension allocated)
      (.singleton (.returnValue (lookupStatement?_sound (actual.source.symm ▸ observed.failedShape.statementFound))
        observed.failedShape.statementForm read))
  have body := sourceAt.frame.body_of_trace actual.header.extended bound
    (FunctionCallBody.Trace.fault executed)
  cases body with
  | fault failed =>
    exact ⟨rawD, global, sourceAt, .globalBody sourceAt.frame.instantiated rfl (sourceAt.dictionary ▸ failed)⟩

end Tests.SourceCoreSelectedLexicalOrdinaryTraces
