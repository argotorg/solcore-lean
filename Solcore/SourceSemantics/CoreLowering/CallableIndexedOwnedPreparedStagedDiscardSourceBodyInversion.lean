import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping

/-! An actual semicolon discard before a supported terminal statement retains
two original Source children. Lookup uniqueness selects the expression trace;
full original body typing supplies its raw type and the remaining terminal
child at the same parameter context. No body execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

/-- A failed prefix returns its exact nested Failure. A successful prefix
retains the actual middle heap and the original remaining statement trace. -/
theorem child_and_tail {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.fault failure) after) ∨
    (∃ childSize tailSize value middle,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.value value) middle ∧
      Size.Statements program registry tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique contains form
  cases trace with
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
    have impossible := (shape actual).symm.trans same
    cases impossible
  | returnUnit actual same =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | returnValue actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | returnFault actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | tail actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | discard actual same child remaining =>
    have equal := (shape actual).symm.trans same
    cases equal
    exact .inr ⟨_, _, _, _, rfl, child, remaining⟩
  | expressionFault actual same child =>
    have equal := (shape actual).symm.trans same
    cases equal
    exact .inl ⟨_, _, rfl, rfl, rfl, child⟩
  | letUninitialized actual same monomorphic extension allocation remaining =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | letInitialized actual same child monomorphic extension allocation remaining =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | letFault actual same monomorphic child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBare actual same _ _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareFault actual same _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareUnbound actual same _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareDangling actual same _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible

private theorem discard_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, final = context ∧
      facts = { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      ExpressionHasType source context expression type := by
  have shape := @statement_shape _ _ _ _ unique contains form
  clear contains form
  cases typed <;> have actualForm := shape (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- Both children use the original raw parameter context. The discard has no
lexical effect, and its ordinary control summary preserves tail completeness. -/
theorem children_typed {invocation : Scope} {context final : SourceSemantics.Context}
    {id next : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression terminal : ExpressionId} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique invocation.source)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (head : Head invocation terminal (next :: rest))
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context (id :: next :: rest) final facts)
    (completes : BodyCompletes expected facts) :
    ∃ firstNode terminalNode,
      invocation.source.lookupExpression? expression = some firstNode ∧
      ExpressionHasType invocation.source context expression firstNode.type ∧
      invocation.source.lookupExpression? terminal = some terminalNode ∧
      terminalNode.type = expected ∧
      ExpressionHasType invocation.source context terminal terminalNode.type := by
  cases typed with
  | @cons _ _ _ _ _ _ _ _ tailFacts first remaining =>
    obtain ⟨firstType, rfl, rfl, firstTyped⟩ := discard_typed unique contains form first
    have tailCompletes : BodyCompletes expected tailFacts := by
      simpa [BodyFacts.cons] using completes
    obtain ⟨terminalNode, terminalFound, resultType, terminalTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head remaining tailCompletes
    obtain ⟨firstNode, firstContains, firstTypeEq⟩ := firstTyped.stored_type
    exact ⟨firstNode, terminalNode, lookupExpression?_complete unique firstContains,
      firstTypeEq ▸ firstTyped, terminalFound, resultType, terminalTyped⟩

/-- The original closure frame and the actual parameter extension supply the
full typing derivation before either expression child is selected. -/
theorem at_parameters {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {invocation : Scope} {id next : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression terminal : ExpressionId}
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source)
    (body : function.body = id :: next :: rest)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (head : Head invocation terminal (next :: rest)) :
    ∃ firstNode terminalNode,
      invocation.source.lookupExpression? expression = some firstNode ∧
      ExpressionHasType invocation.source context expression firstNode.type ∧
      invocation.source.lookupExpression? terminal = some terminalNode ∧
      terminalNode.type = function.resultType ∧
      ExpressionHasType invocation.source context terminal terminalNode.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [body, ← source] at typed
  exact children_typed unique contains form head typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
