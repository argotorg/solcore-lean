import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! The actual while statement retains its complete finite loop and only the
suffix reached after fallthrough. Every child has its original strict grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion
open Frontend SourceInference Staging.Recursive

theorem loop_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ loopSize value,
      size = Size.stepSize [loopSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.While program registry loopSize invocation context environment before
        condition statements (.returned value) after) ∨
    (∃ loopSize failure,
      size = Size.stepSize [loopSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.While program registry loopSize invocation context environment before
        condition statements (.fault failure) after) ∨
    (∃ loopSize tailSize middle,
      size = Size.stepSize [loopSize, tailSize] ∧
      Size.While program registry loopSize invocation context environment before
        condition statements (.fallthrough environment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .whileLoop condition statements := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _ | letFault actual same _ _
  | assignBare actual same _ _ _ _ | assignBareFault actual same _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | whileReturned actual same loop =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, loop⟩
  | whileFault actual same loop =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, rfl, rfl, rfl, loop⟩)
  | whileFallthrough actual same loop next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr ⟨_, _, _, rfl, loop, next⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion
