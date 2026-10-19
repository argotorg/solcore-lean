import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Actual for statements retain ordered initialization, each finite iteration,
and only the suffix reached after restoring the outer lexical scope. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceInversion
open Frontend SourceInference Staging.Recursive

theorem initial_loop_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ initialSize failedContext failure,
      size = Size.stepSize [initialSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.ForItems program registry initialSize invocation context environment before initial failedContext (.fault failure) after) ∨
    (∃ initialSize loopSize loopContext loopEnvironment initialized value,
      size = Size.stepSize [initialSize, loopSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.ForItems program registry initialSize invocation context environment before initial loopContext (.done loopEnvironment) initialized ∧
      Size.ForLoop program registry loopSize invocation loopContext loopEnvironment initialized condition post body (.returned value) after) ∨
    (∃ initialSize loopSize loopContext loopEnvironment initialized failure,
      size = Size.stepSize [initialSize, loopSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.ForItems program registry initialSize invocation context environment before initial loopContext (.done loopEnvironment) initialized ∧
      Size.ForLoop program registry loopSize invocation loopContext loopEnvironment initialized condition post body (.fault failure) after) ∨
    (∃ initialSize loopSize tailSize loopContext loopEnvironment initialized middle,
      size = Size.stepSize [initialSize, loopSize, tailSize] ∧
      Size.ForItems program registry initialSize invocation context environment before initial loopContext (.done loopEnvironment) initialized ∧
      Size.ForLoop program registry loopSize invocation loopContext loopEnvironment initialized condition post body (.fallthrough loopEnvironment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .forLoop initial condition post body := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _ | letFault actual same _ _
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
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | ifConditionFault actual same _ | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | forInitializerFault actual same initialTrace =>
      cases (shape actual).symm.trans same
      exact .inl ⟨_, _, _, rfl, rfl, rfl, initialTrace⟩
  | forReturned actual same initialTrace loop =>
      cases (shape actual).symm.trans same
      exact .inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, initialTrace, loop⟩)
  | forFault actual same initialTrace loop =>
      cases (shape actual).symm.trans same
      exact .inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, initialTrace, loop⟩))
  | forFallthrough actual same initialTrace loop next =>
      cases (shape actual).symm.trans same
      exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, rfl, initialTrace, loop, next⟩))

/-- Iteration-local and post-header bindings cannot replace the loop environment. -/
theorem fallthrough_environment {program : Program} {registry : Registry} {invocation : Scope}
    {context : SourceSemantics.Context} {environment returned : Dynamic.Environment}
    {before after : Dynamic.Heap} {condition : ExpressionId} {post : List ForItemForm} {body : List StatementId}
    {size : Nat}
    (trace : Size.ForLoop program registry size invocation context environment before condition post body
      (.fallthrough returned) after) : returned = environment := by
  induction size using Nat.strongRecOn generalizing before after with
  | ind size ih =>
    cases trace with
    | finished => rfl
    | forBreakFromBody => rfl
    | iterate _ _ _ next | continueIterate _ _ _ next => exact ih _ (Size.child_lt_stepSize (by simp)) next

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceInversion
