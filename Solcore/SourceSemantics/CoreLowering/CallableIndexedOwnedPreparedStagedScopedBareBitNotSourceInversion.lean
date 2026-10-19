import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! The actual unary statement supplies either its unchanged-heap fault or
its genuine write and suffix. No right-hand expression is introduced. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareBitNotSourceInversion
open Frontend SourceInference Staging.Recursive

theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (bare : assignment.target.projections = [])
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ reason, size = Size.stepSize [] ∧ finalContext = context ∧
      outcome = .fault (.semantic reason) ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
        environment before assignment.target reason before) ∨
    (∃ tailSize target updated written,
      size = Size.stepSize [tailSize] ∧ BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      Size.StatementsIn program registry mode tailSize invocation context environment written rest finalContext outcome after) := by
  have shape {other : StatementNode} (present : ContainsStatement invocation.source id other) :
      other.form = .assignBitNot assignment := by
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | bitNotBare actual same snapshot write remaining =>
      cases (shape actual).symm.trans same
      exact .inr ⟨_, _, _, _, rfl, snapshot, write, remaining⟩
  | bitNotBareFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .inl ⟨_, rfl, rfl, rfl, rfl, failed⟩
  | bitNotProjected actual same projected _ _ _ _
  | bitNotProjectedRootFault actual same projected _
  | bitNotProjectedKeysFault actual same projected _ _
  | bitNotProjectedGetterFault actual same projected _ _ =>
      cases (shape actual).symm.trans same
      exact (projected bare).elim
  | breaking actual same | continuing actual same
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | ifReturned actual same _ _ | ifFault actual same _ _ | ifFallthrough actual same _ _ _
  | letGeneralized actual same _ _ _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | letFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareOperands actual same _ _ _ _ _ _ _
  | assignBareFault actual same _ _ | assignBareUnbound actual same _ _
  | assignBareDangling actual same _ _ _ =>
      cases (shape actual).symm.trans same

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareBitNotSourceInversion
