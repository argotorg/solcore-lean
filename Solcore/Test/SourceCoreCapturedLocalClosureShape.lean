import Solcore.Test.SourceCoreCapturedLocalFixture
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! The actual factory Source trace identifies the returned ordinary closure.
The witness keeps the captured environment produced by that same trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedLocal
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem statement_roots_injective {left right : List StatementId}
    (equal : left.map NodeId.statement = right.map NodeId.statement) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp at equal ⊢
  | cons head rest ih =>
    cases right with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.map_cons, List.cons.injEq] at equal
      obtain ⟨same, tails⟩ := equal
      cases same
      simp only [ih tails]

private theorem returned_expression
    {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression : ExpressionId} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment
      before (id :: rest) finalContext (.returned value) after) :
    Dynamic.ExpressionEvaluates program context scope.evidence scope.source environment before
      expression value after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
  | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
  | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
  | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
  | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnUnit contains otherForm =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | returnValue contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact child.sound.value_plain
  | tail contains otherForm _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | discard contains otherForm _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letUninitialized contains otherForm _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible
  | assignBare contains otherForm _ _ _ _
  | assignProjected contains otherForm _ _ _ _ _ _
  | bitNotBare contains otherForm _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem lambda_shape
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .lambda [] .word body)
    (uncoerced : node.coercions = [])
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    ∃ function : Dynamic.Closure,
      value = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      function.captured = environment ∧ function.context = context ∧ after = before := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | generalizedLocal contains otherForm _ _ _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem initialized_read
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {word : Core.Word}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (uncoerced : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location { type := .word, value := some (.word word) })
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    value = .word word ∧ after = before := by
  have same {other : ExpressionNode} (contains : ContainsExpression source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | intro contains raw coercions =>
    have nodeEq := same contains
    cases nodeEq
    rw [uncoerced] at coercions
    cases coercions
    rw [form] at raw
    cases raw with
    | «local» _ actualLookup actualRead _ initialized =>
      have sameLocation := actualLookup.functional lookup
      subst_vars
      have sameCell := actualRead.functional read
      cases sameCell
      exact ⟨Option.some.inj initialized.symm, rfl⟩
    | localEmptyMapping _ actualLookup actualRead _ _ empty _ =>
      have sameLocation := actualLookup.functional lookup
      subst_vars
      have sameCell := actualRead.functional read
      cases sameCell
      cases empty
  | generalizedLocal contains otherForm _ actualLookup actualRead descriptor _ _ _ =>
    have nodeEq := same contains
    cases nodeEq
    rw [form] at otherForm
    cases otherForm
    have sameLocation := actualLookup.functional lookup
    subst_vars
    have sameCell := actualRead.functional read
    cases sameCell
    cases descriptor

/-- Any successful actual factory Source call returns the very closure created
by its terminal lambda after the local cell allocation. -/
theorem ActualHeader.returned_capture
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word} {source : Dynamic.Value}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry
        (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
          fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected))
      size invocation context before (.global global) [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word ∧
      BinderExtends actual.header.function.source.owner actual.header.context observed.localBinder function.context ∧
      ∃ location, Dynamic.Environment.LooksUp function.captured observed.localBinder.id location ∧
        Dynamic.Heap.Reads after location { type := .word, value := some (.word word) } := by
  have parameters : actual.header.function.parameters = [observed.shape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry
    (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  have bodyEq : actual.header.function.body = [observed.shape.initialized.id, observed.statement.id] := by
    apply statement_roots_injective
    rw [← actual.header.agreement.roots, actual.source, observed.roots]
    rfl
  have initializedFound : child.source.lookupStatement? observed.shape.initialized.id =
      some observed.shape.initialized := by
    rw [sourceEq, actual.source]
    exact observed.shape.initializedFound
  have statementFound : child.source.lookupStatement? observed.statement.id = some observed.statement := by
    rw [sourceEq, actual.source]
    exact observed.foundStatement
  have expressionFound : child.source.lookupExpression? observed.expression.id = some observed.expression := by
    rw [sourceEq, actual.source]
    exact observed.foundExpression
  have resultType : actual.header.function.resultType = .function .unit .word := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact observed.resultType
  rw [resultType] at converted
  cases converted
  rw [parameters] at parametersAllocated
  cases parametersAllocated with
  | cons parameterAllocation remaining =>
    cases remaining
    have parameterCell := parameterAllocation.reads_new
    simp only [observed.binderScheme, TypeSystem.Scheme.mono] at parameterCell
    rw [bodyEq] at body
    have same {other : StatementNode}
        (contains : ContainsStatement child.source observed.shape.initialized.id other) :
        other = observed.shape.initialized :=
      Option.some.inj ((lookupStatement?_complete unique contains).symm.trans initializedFound)
    cases body with
    | forReturned contains otherForm _ _ | forFallthrough contains otherForm _ _ _
    | matchReturned contains otherForm _ | matchFallthrough contains otherForm _ _
    | blockReturned contains otherForm _ | blockFallthrough contains otherForm _ _
    | whileReturned contains otherForm _ | whileFallthrough contains otherForm _ _
    | ifReturned contains otherForm _ _ | ifFallthrough contains otherForm _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | returnUnit contains otherForm =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | returnValue contains otherForm _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | discard contains otherForm _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | letUninitialized contains otherForm _ _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | assignBare contains otherForm _ _ _ _
    | assignProjected contains otherForm _ _ _ _ _ _
    | bitNotBare contains otherForm _ _ _ =>
      have impossible := (same contains) ▸ otherForm
      rw [observed.shape.initializedForm] at impossible
      cases impossible
    | letInitialized contains form initializer _mono extended allocated next =>
      rename_i localLocation
      have nodeEq := same contains
      cases nodeEq
      rw [observed.shape.initializedForm] at form
      cases form
      obtain ⟨sameValue, sameHeap⟩ := initialized_read unique
        (by rw [sourceEq, actual.source]; exact observed.shape.initialReadFound)
        observed.shape.initialReadForm observed.shape.initialReadCoercions
        .head parameterCell initializer.sound.value_plain
      subst_vars
      obtain ⟨function, valueEq, params, result, captures, contextEq, heapEq⟩ :=
        lambda_shape unique expressionFound observed.lambda observed.coercions
          (returned_expression unique statementFound observed.returnStatement next)
      refine ⟨function, valueEq, params, result, ?_, localLocation, ?_, ?_⟩
      · rw [contextEq, ← sourceEq]
        exact extended
      · rw [captures]
        exact .head
      · rw [heapEq]
        simpa only [observed.localScheme, TypeSystem.Scheme.mono] using allocated.reads_new

/-- The structural consequence used by generic direct invocation. -/
theorem ActualHeader.returned_closure
    {fixture : CompiledFixture} {observed : ObservedFactory fixture}
    (actual : ActualHeader fixture observed.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word} {source : Dynamic.Value}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry
        (RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
          fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected))
      size invocation context before (.global global) [.word word] (.value source) after) :
    ∃ function : Dynamic.Closure,
      source = .closure function ∧ function.parameters = [] ∧ function.resultType = .word := by
  obtain ⟨function, value, parameters, result, _extended, _location, _captured, _cell⟩ :=
    actual.returned_capture sourceAt applied
  exact ⟨function, value, parameters, result⟩

end Tests.SourceCoreCapturedLocal
