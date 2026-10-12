import Solcore.Test.SourceCoreInitialLexicalFailureBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.Staging.RecursiveErasure
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering

private theorem local_fault {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {failure : Staging.Recursive.Failure} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location {type := .word, value := none})
    (trace : Staging.Recursive.Size.Expression program registry size scope context environment before id (.fault failure) after) :
    failure = .semantic (.uninitializedLocation location) ∧ after = before := by
  have same {other : ExpressionNode} (contains : ContainsExpression scope.source id other) : other = node :=
    Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases trace with
  | atomicFault contains atomic uncoerced raw =>
    have nodeEq := same contains
    cases nodeEq
    rw [form] at raw
    cases raw with
    | localUnbound _ missing => exact False.elim (missing.excludes_lookup lookup)
    | localDangling _ actual dangling =>
      have eq := actual.functional lookup
      subst_vars
      exact False.elim (dangling.excludes_read read)
    | localUninitialized _ actual _ _ _ _ =>
      have eq := actual.functional lookup
      subst_vars
      exact ⟨rfl, rfl⟩
  | group occurrence _ | pairLeftFault occurrence _ | pairRightFault occurrence _ _
  | tupleFault occurrence _ | unaryOperandFault occurrence _ | unaryInvalid occurrence _ _
  | binaryLeftFault occurrence _ | binaryLeftInvalid occurrence _ _
  | binaryRightFault occurrence _ _ _ | binaryInvalid occurrence _ _ _ _
  | conditional occurrence _ _ | conditionalFault occurrence _
  | calleeFault occurrence _ | notCallable occurrence _ _ | rejected occurrence _ _
  | argumentsFault occurrence _ _ _ | sourceArity occurrence _ _ _ _
  | applied occurrence _ _ _ _ _ _ =>
    obtain ⟨other, contains, otherForm, _requirements, _coercions⟩ := occurrence
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem return_fault {program : Program} {registry : Staging.Recursive.Registry}
    {scope : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    {failure : Staging.Recursive.Failure} {size : Nat}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (trace : Staging.Recursive.Size.Statements program registry size scope context environment before
      (id :: rest) finalContext (.fault failure) after) :
    ∃ childSize, Staging.Recursive.Size.Expression program registry childSize scope context environment before
      expression (.fault failure) after := by
  have same {other : StatementNode} (contains : ContainsStatement scope.source id other) : other = node :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  cases trace with
  | returnFault contains otherForm child =>
    have expressionEq := (same contains) ▸ otherForm
    rw [form] at expressionEq
    cases expressionEq
    exact ⟨_, child⟩
  | expressionFault contains otherForm _ | letFault contains otherForm _ _
  | discard contains otherForm _ _ | letUninitialized contains otherForm _ _ _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

/-- The first failed Source call allocates the absent cell before reading it;
its returned heap is exactly that allocation's heap. -/
theorem ActualHeader.failed_heap
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.failedRow.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      size invocation context before (.global global) [] (.fault failure) after) :
    ∃ location, failure = .semantic (.uninitializedLocation location) ∧
      Dynamic.Heap.Allocates before .word none location after ∧
      Dynamic.Heap.Reads after location {type := .word, value := none} := by
  have parameters : actual.header.function.parameters = [] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.failedShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  rw [actual.failed_result_type] at converted
  cases converted
  rw [parameters] at parametersAllocated
  cases parametersAllocated
  rw [actual.failed_statements] at body
  have declaredFound : child.source.lookupStatement? observed.failedShape.declared.id = some observed.failedShape.declared := by
    rw [sourceEq, actual.source]; exact observed.failedShape.declaredFound
  have same {other : StatementNode} (contains : ContainsStatement child.source observed.failedShape.declared.id other) :
      other = observed.failedShape.declared :=
    Option.some.inj ((lookupStatement?_complete unique contains).symm.trans declaredFound)
  cases body with
  | returnFault contains otherForm _ | expressionFault contains otherForm _
  | letFault contains otherForm _ _ | discard contains otherForm _ _
  | letInitialized contains otherForm _ _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [observed.failedShape.declaredForm] at impossible
    cases impossible
  | letUninitialized contains form _mono _extended allocated next =>
    rename_i location
    have nodeEq := same contains
    cases nodeEq
    rw [observed.failedShape.declaredForm] at form
    cases form
    obtain ⟨childSize, expression⟩ := return_fault unique
      (by rw [sourceEq, actual.source]; exact observed.failedShape.statementFound)
      observed.failedShape.statementForm next
    have cell := allocated.reads_new
    simp only [observed.failedShape.binderScheme, TypeSystem.Scheme.mono] at cell
    obtain ⟨failureEq, heapEq⟩ := local_fault unique
      (by rw [sourceEq, actual.source]; exact observed.failedShape.readFound)
      observed.failedShape.readForm .head cell expression
    subst after
    refine ⟨location, failureEq, ?_, cell⟩
    simpa only [observed.failedShape.binderScheme, TypeSystem.Scheme.mono] using allocated

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

/-- The following identity call only allocates its actual Word parameter.
Any earlier cell therefore remains present with its original contents. -/
theorem ActualHeader.identity_heap
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    (actual : ActualHeader fixture observed.identityRow.row)
    {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
    {before after : Dynamic.Heap} {word : Core.Word}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt actual.header rawD global)
    {size : Nat}
    (applied : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      size invocation context before (.global global) [.word word] (.value (.word word)) after) :
    ∃ location, Dynamic.Heap.Allocates before .word (some (.word word)) location after := by
  have parameters : actual.header.function.parameters = [observed.identityShape.binder] := by
    rw [actual.header.parameters, ← actual.header.inputs, actual.source, observed.identityShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, parametersAllocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ actual.header.unique
  rw [actual.identity_result_type] at converted
  cases converted
  rw [parameters] at parametersAllocated
  cases parametersAllocated with
  | cons allocated remaining =>
    cases remaining
    have cell := allocated.reads_new
    simp only [observed.identityShape.binderScheme, TypeSystem.Scheme.mono] at cell
    rw [actual.identity_statements] at body
    have expression := returned_expression unique
      (by rw [sourceEq, actual.source]; exact observed.identityShape.statementFound)
      observed.identityShape.statementForm body
    obtain ⟨_word, sameHeap⟩ := initialized_read unique
      (by rw [sourceEq, actual.source]; exact observed.identityShape.readFound)
      observed.identityShape.readForm observed.identityShape.readCoercions .head cell expression
    subst after
    exact ⟨_, by simpa only [observed.identityShape.binderScheme, TypeSystem.Scheme.mono] using allocated⟩

end Tests.SourceCoreInitialLexicalFailure
