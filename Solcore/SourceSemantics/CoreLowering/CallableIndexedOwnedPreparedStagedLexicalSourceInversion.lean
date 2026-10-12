import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion

/-! Actual lexical Source steps expose the initializer and the allocated tail.
The tail keeps its extended context and final context; no body execution law
or chosen allocation is supplied separately. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases nodeEq
  exact same

private theorem extension_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binder : TypedBinder}
    (left : BinderExtends owner context binder first)
    (right : BinderExtends owner context binder second) : first = second := by
  cases left
  cases right
  rfl

theorem absent {program : Program} {registry : Registry} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Size.Statements program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | letInitialized actual same _ _ _ _ _ | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letUninitialized actual same _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact ⟨_, _, _, rfl, allocated, remaining⟩

theorem initialized {program : Program} {registry : Registry} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.fault failure) after) ∨
    (∃ childSize tailSize value location middle bound,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Size.Statements program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letInitialized actual same child _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact .inr ⟨_, _, _, _, _, _, rfl, child, allocated, remaining⟩
  | letFault actual same _ child =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, child⟩

theorem return_unit {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | returnUnit actual same => exact ⟨rfl, rfl, rfl⟩
  | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalSourceInversion
