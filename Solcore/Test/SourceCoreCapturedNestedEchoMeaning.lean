import Solcore.Test.SourceCoreCapturedNestedCommon
import Solcore.Test.SourceCoreCapturedNestedSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation
import Solcore.SourceSemantics.Staging.RecursiveErasure

/-! The actual echo Source trace preserves the complete ordered input value,
including duplicate mapping keys and repeated captured function values. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCapturedNested
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
  | assignBare contains otherForm _ _ _ _ =>
    have impossible := (same contains) ▸ otherForm
    rw [form] at impossible
    cases impossible

private theorem initialized_read
    {program : Program} {source : TypedSource} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : ExpressionId} {node : ExpressionNode}
    {value : Dynamic.Value} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {type : TypeSystem.Ty} {argument : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (uncoerced : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads before location { type := type, value := some argument })
    (trace : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    value = argument ∧ after = before := by
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

/-- The genuine echo body returns the same ordered Source mapping value.
Only its real parameter allocation intervenes; the public encoder is not used
as a Source evaluator. -/
theorem SourceCall.echo_value
    {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
    {invocation : Staging.Recursive.Scope} {before after : Dynamic.Heap}
    {argument source : Dynamic.Value}
    (trace : SourceCall support support.readHeader.header invocation before [argument] (.value source) after) :
    source = argument := by
  obtain ⟨rawD, global, size, sourceAt, applied⟩ := trace
  have parameters : support.readHeader.header.function.parameters = [observed.readShape.binder] := by
    rw [support.readHeader.header.parameters, ← support.readHeader.header.inputs,
      support.readHeader.source, observed.readShape.inputs]
  obtain ⟨bodySize, child, environment, bound, finalContext, bodyOutcome,
      selected, allocated, body, converted, _smaller⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalNamedInvocationPreservation.body_prefix
      sourceAt fixture.source_wellFormed (by simp [parameters]) applied
  have sourceEq := (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)).source selected
  have unique : NodeOccurrencesUnique child.source := sourceEq ▸ support.readHeader.header.unique
  have bodyEq : support.readHeader.header.function.body = [observed.readShape.statement.id] := by
    apply statement_roots_injective
    rw [← support.readHeader.header.agreement.roots, support.readHeader.source, observed.readShape.roots]
    rfl
  rw [support.readHeader.read_result_type] at converted
  cases converted
  rw [parameters] at allocated
  cases allocated with
  | cons allocated remaining =>
    cases remaining
    rw [bodyEq] at body
    have expression := returned_expression unique
      (by rw [sourceEq, support.readHeader.source]; exact observed.readShape.statementFound)
      observed.readShape.statementForm body
    exact (initialized_read unique
      (by rw [sourceEq, support.readHeader.source]; exact observed.readShape.readFound)
      observed.readShape.readForm observed.readShape.readCoercions .head allocated.reads_new expression).1

end Tests.SourceCoreCapturedNested
