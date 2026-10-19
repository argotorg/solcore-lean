import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! A control statement stops before its suffix and retains its exact entry state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend SourceInference

theorem Size.StatementsIn.breaking_view {program : Program} {registry : Registry}
    {mode : Bool} {size : Nat} {scope : Scope} {context finalContext : Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .breakStmt)
    (trace : Size.StatementsIn program registry mode size scope context environment before
      (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .breaking environment ∧ after = before := by
  have shape : ∀ {other}, ContainsStatement scope.source id other → other.form = .breakStmt := by
    intro other present
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | returnUnit actual same  =>
      cases (shape actual).symm.trans same
  | continuing actual same  =>
      cases (shape actual).symm.trans same
  | breaking _ _ => exact ⟨rfl, rfl, rfl⟩
  | returnValue actual same _ =>
      cases (shape actual).symm.trans same
  | returnFault actual same _ =>
      cases (shape actual).symm.trans same
  | tail actual same _ =>
      cases (shape actual).symm.trans same
  | discard actual same _ _ =>
      cases (shape actual).symm.trans same
  | expressionFault actual same _ =>
      cases (shape actual).symm.trans same
  | discardValue actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifConditionFault actual same _ =>
      cases (shape actual).symm.trans same
  | ifReturned actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifContinuing actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifBreaking actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifFallthrough actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | blockReturned actual same _ =>
      cases (shape actual).symm.trans same
  | blockContinuing actual same _ =>
      cases (shape actual).symm.trans same
  | blockBreaking actual same _ =>
      cases (shape actual).symm.trans same
  | blockFault actual same _ =>
      cases (shape actual).symm.trans same
  | blockFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | matchReturned actual same _ =>
      cases (shape actual).symm.trans same
  | matchContinuing actual same _ =>
      cases (shape actual).symm.trans same
  | matchBreaking actual same _ =>
      cases (shape actual).symm.trans same
  | matchFault actual same _ =>
      cases (shape actual).symm.trans same
  | matchFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | forInitializerFault actual same _ =>
      cases (shape actual).symm.trans same
  | forReturned actual same _ _ =>
      cases (shape actual).symm.trans same
  | forFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | forFallthrough actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | whileReturned actual same _ =>
      cases (shape actual).symm.trans same
  | whileFault actual same _ =>
      cases (shape actual).symm.trans same
  | whileFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBare actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBareFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjected actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedRootFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedKeysFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedGetterFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjected actual same _ _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedRootFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedKeysFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedGetterFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedRhsFault actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedWriteFault actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBare actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBareFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignBareOperands actual same _ _ _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBareUnbound actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignBareDangling actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | letGeneralized actual same _ _ _ _ _
  | letUninitialized actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | letInitialized actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | letFault actual same _ _ =>
      cases (shape actual).symm.trans same

theorem Size.StatementsIn.continuing_view {program : Program} {registry : Registry}
    {mode : Bool} {size : Nat} {scope : Scope} {context finalContext : Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique scope.source)
    (found : scope.source.lookupStatement? id = some node)
    (form : node.form = .continueStmt)
    (trace : Size.StatementsIn program registry mode size scope context environment before
      (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .continuing environment ∧ after = before := by
  have shape : ∀ {other}, ContainsStatement scope.source id other → other.form = .continueStmt := by
    intro other present
    have same := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
    cases same
    exact form
  cases trace with
  | returnUnit actual same  =>
      cases (shape actual).symm.trans same
  | continuing _ _ => exact ⟨rfl, rfl, rfl⟩
  | breaking actual same  =>
      cases (shape actual).symm.trans same
  | returnValue actual same _ =>
      cases (shape actual).symm.trans same
  | returnFault actual same _ =>
      cases (shape actual).symm.trans same
  | tail actual same _ =>
      cases (shape actual).symm.trans same
  | discard actual same _ _ =>
      cases (shape actual).symm.trans same
  | expressionFault actual same _ =>
      cases (shape actual).symm.trans same
  | discardValue actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifConditionFault actual same _ =>
      cases (shape actual).symm.trans same
  | ifReturned actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifContinuing actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifBreaking actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | ifFallthrough actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | blockReturned actual same _ =>
      cases (shape actual).symm.trans same
  | blockContinuing actual same _ =>
      cases (shape actual).symm.trans same
  | blockBreaking actual same _ =>
      cases (shape actual).symm.trans same
  | blockFault actual same _ =>
      cases (shape actual).symm.trans same
  | blockFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | matchReturned actual same _ =>
      cases (shape actual).symm.trans same
  | matchContinuing actual same _ =>
      cases (shape actual).symm.trans same
  | matchBreaking actual same _ =>
      cases (shape actual).symm.trans same
  | matchFault actual same _ =>
      cases (shape actual).symm.trans same
  | matchFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | forInitializerFault actual same _ =>
      cases (shape actual).symm.trans same
  | forReturned actual same _ _ =>
      cases (shape actual).symm.trans same
  | forFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | forFallthrough actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | whileReturned actual same _ =>
      cases (shape actual).symm.trans same
  | whileFault actual same _ =>
      cases (shape actual).symm.trans same
  | whileFallthrough actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBare actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBareFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjected actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedRootFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedKeysFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | bitNotProjectedGetterFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjected actual same _ _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedRootFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedKeysFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedGetterFault actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedRhsFault actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignProjectedWriteFault actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBare actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBareFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignBareOperands actual same _ _ _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | assignBareUnbound actual same _ _ =>
      cases (shape actual).symm.trans same
  | assignBareDangling actual same _ _ _ =>
      cases (shape actual).symm.trans same
  | letGeneralized actual same _ _ _ _ _
  | letUninitialized actual same _ _ _ _ =>
      cases (shape actual).symm.trans same
  | letInitialized actual same _ _ _ _ _ =>
      cases (shape actual).symm.trans same
  | letFault actual same _ _ =>
      cases (shape actual).symm.trans same

end Solcore.SourceSemantics.Staging.Recursive
