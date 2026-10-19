import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Projected unary inversion retains the actual key endpoint and written suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedBitNotSourceInversion
open Frontend SourceInference Staging.Recursive

inductive Result (program : Program) (registry : Registry) (mode : Bool) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (rest : List StatementId) :
    Nat → SourceSemantics.Context → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize []) context (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [keysSize]) context (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [keysSize]) context (.fault (.semantic reason)) after
  | success {keysSize tailSize values target targetHeap updated written finalContext outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        targetHeap target updated written)
      (next : Size.StatementsIn program registry mode tailSize invocation context environment written rest finalContext outcome after) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [keysSize, tailSize]) finalContext outcome after

theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (projected : assignment.target.projections ≠ [])
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    Result program registry mode invocation context environment before assignment rest size finalContext outcome after := by
  have shape {other : StatementNode} (present : ContainsStatement invocation.source id other) :
      other.form = .assignBitNot assignment := by
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
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
  | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ | assignBareFault actual same _ _
  | assignBareOperands actual same _ _ _ _ _ _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _ | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _ | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | letFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBare actual same snapshot _ _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
  | bitNotBareFault actual same empty _ =>
      cases (shape actual).symm.trans same
      exact (projected empty).elim
  | bitNotProjected actual same _ keys snapshot write next =>
      cases (shape actual).symm.trans same
      exact .success keys snapshot write next
  | bitNotProjectedRootFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .rootFault failed
  | bitNotProjectedKeysFault actual same _ ready keys =>
      cases (shape actual).symm.trans same
      exact .keysFault ready keys
  | bitNotProjectedGetterFault actual same _ keys failed =>
      cases (shape actual).symm.trans same
      exact .getterFault keys failed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedBitNotSourceInversion
