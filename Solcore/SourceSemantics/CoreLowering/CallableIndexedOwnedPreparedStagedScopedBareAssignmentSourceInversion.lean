import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Original bare assignment traces retain the pre-RHS cell snapshot and the
actual post-RHS write. A live target excludes target lookup failures without
assuming anything about the RHS outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem target_functional {environment : Dynamic.Environment} {heap : Dynamic.Heap}
    {place : PlaceResolution} {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left)
    (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      have locationEq := leftLookup.functional rightLookup
      cases locationEq
      have cellEq := leftRead.functional rightRead
      cases cellEq
      have valueEq := leftValue.functional rightValue
      cases valueEq
      rfl

/-- The actual Source rule selects either a failed RHS or a successful RHS,
its write and the remaining statements. The pre-RHS target is unchanged. -/
theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment .equal rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize tailSize value middle written updated,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected value replacement)
        middle target updated written ∧
      Size.StatementsIn program registry mode tailSize invocation context environment written rest finalContext outcome after) := by
  have shape {other : StatementNode} (present : ContainsStatement invocation.source id other) :
      other.form = .assignValue assignment .equal rhs := by
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | assignBare actual same actualSnapshot child write remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have targetEq := target_functional snapshot actualSnapshot
      cases targetEq
      exact .inr ⟨_, _, _, _, _, _, rfl, child, write, remaining⟩
  | assignBareFault actual same _ child =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, child⟩
  | assignBareUnbound actual same _ missing =>
      have equal := (shape actual).symm.trans same
      cases equal
      cases snapshot with
      | intro _ lookup _ _ => exact False.elim (missing.excludes_lookup lookup)
  | assignBareDangling actual same _ lookup missing =>
      have equal := (shape actual).symm.trans same
      cases equal
      cases snapshot with
      | intro _ actualLookup read _ =>
          have locationEq := lookup.functional actualLookup
          cases locationEq
          exact False.elim (missing.excludes_read read)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
