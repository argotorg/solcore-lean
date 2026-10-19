import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! Projected assignment inversion retains each evaluated key, the getter
snapshot, the reached RHS heap and the actual statement suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion
open Frontend SourceInference Staging.Recursive

inductive Result (program : Program) (registry : Registry) (mode : Bool) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) (rest : List StatementId) :
    Nat → SourceSemantics.Context → BodyOutcome → Dynamic.Heap → Prop where
  | rootFault {reason}
      (failed : ProjectedTarget.RootFault environment before assignment.target reason) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize []) context (.fault (.semantic reason)) before
  | keysFault {keysSize failure after}
      (ready : ProjectedTarget.RootReady environment before assignment.target)
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.fault failure) after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [keysSize]) context (.fault failure) after
  | getterFault {keysSize values reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) after)
      (failed : ProjectedTarget.GetterFault environment before after assignment.target values reason) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [keysSize]) context (.fault (.semantic reason)) after
  | rhsFault {keysSize childSize values target targetHeap failure after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.fault failure) after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [keysSize, childSize]) context (.fault failure) after
  | writeFault {keysSize childSize values target targetHeap right reason after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) after)
      (failed : ProjectedTarget.WriteFault operator target right after reason) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [keysSize, childSize]) context (.fault (.semantic reason)) after
  | success {keysSize childSize tailSize values target targetHeap right middle updated written finalContext outcome after}
      (keys : Size.Expressions program registry keysSize invocation context environment before
        (ProjectedTarget.keys assignment.target.projections) (.values values) targetHeap)
      (snapshot : ProjectedTarget.Snapshot environment before targetHeap assignment.target values target)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected right replacement)
        middle target updated written)
      (next : Size.StatementsIn program registry mode tailSize invocation context environment written rest finalContext outcome after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [keysSize, childSize, tailSize]) finalContext outcome after

theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (projected : assignment.target.projections ≠ [])
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    Result program registry mode invocation context environment before assignment operator rhs rest size finalContext outcome after := by
  have shape {other : StatementNode} (present : ContainsStatement invocation.source id other) :
      other.form = .assignValue assignment operator rhs := by
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
  | letGeneralized actual same _ _ _ _ _
  | letUninitialized actual same _ _ _ _ | letInitialized actual same _ _ _ _ _
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | assignBare actual same snapshot _ _ _
  | assignBareOperands actual same snapshot _ _ _ _ _ _
  | assignBareFault actual same snapshot _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
  | assignBareUnbound actual same empty _
  | assignBareDangling actual same empty _ _ =>
      cases (shape actual).symm.trans same
      exact (projected empty).elim
  | assignProjected actual same _ keys snapshot child write next =>
      cases (shape actual).symm.trans same
      exact .success keys snapshot child write next
  | assignProjectedRootFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .rootFault failed
  | assignProjectedKeysFault actual same _ ready keys =>
      cases (shape actual).symm.trans same
      exact .keysFault ready keys
  | assignProjectedGetterFault actual same _ keys failed =>
      cases (shape actual).symm.trans same
      exact .getterFault keys failed
  | assignProjectedRhsFault actual same _ keys snapshot child =>
      cases (shape actual).symm.trans same
      exact .rhsFault keys snapshot child
  | assignProjectedWriteFault actual same _ keys snapshot child failed =>
      cases (shape actual).symm.trans same
      exact .writeFault keys snapshot child failed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion
