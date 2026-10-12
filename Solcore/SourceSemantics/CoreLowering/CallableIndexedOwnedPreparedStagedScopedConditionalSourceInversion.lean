import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! The actual conditional trace identifies its chosen arm, executed prefix,
strict child grades and restored outer context. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
open Frontend SourceInference Staging.Recursive

theorem children {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ testSize failure,
      size = Size.stepSize [testSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.fault failure) after) ∨
    (∃ testSize branchSize truth value middle innerContext,
      size = Size.stepSize [testSize, branchSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.value (.bool truth)) middle ∧
      Size.StatementsIn program registry false branchSize invocation context environment middle
        (if truth then thenBody else elseBody.getD []) innerContext (.returned value) after) ∨
    (∃ testSize branchSize truth failure middle innerContext,
      size = Size.stepSize [testSize, branchSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.value (.bool truth)) middle ∧
      Size.StatementsIn program registry false branchSize invocation context environment middle
        (if truth then thenBody else elseBody.getD []) innerContext (.fault failure) after) ∨
    (∃ testSize branchSize tailSize truth middle branchHeap innerContext innerEnvironment,
      size = Size.stepSize [testSize, branchSize, tailSize] ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.value (.bool truth)) middle ∧
      Size.StatementsIn program registry false branchSize invocation context environment middle
        (if truth then thenBody else elseBody.getD []) innerContext (.fallthrough innerEnvironment) branchHeap ∧
      Size.StatementsIn program registry mode tailSize invocation context environment branchHeap
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .ifThen condition thenBody elseBody := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _ | letFault actual same _ _
  | assignBare actual same _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | ifConditionFault actual same test =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, test⟩
  | ifReturned actual same test branch =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, test, branch⟩)
  | ifFault actual same test branch =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, test, branch⟩))
  | ifFallthrough actual same test branch next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, test, branch, next⟩))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
