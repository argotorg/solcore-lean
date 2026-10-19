import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! An actual semicolon discard before a supported terminal statement retains
two original Source children. Lookup uniqueness selects the expression trace;
full original body typing supplies its raw type and the remaining terminal
child at the same parameter context. No body execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive

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
theorem child_and_tail {program : Program} {registry : Registry} {mode semicolon : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression semicolon)
    (discarded : semicolon = true ∨ mode = false)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.fault failure) after) ∨
    (∃ childSize tailSize value middle,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.value value) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique contains form
  cases trace with
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | ifReturned actual same _ _ | ifFault actual same _ _
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
    have equal := (shape actual).symm.trans same
    cases equal
    simp at discarded
  | discardValue actual same child remaining
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
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _ =>
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


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
