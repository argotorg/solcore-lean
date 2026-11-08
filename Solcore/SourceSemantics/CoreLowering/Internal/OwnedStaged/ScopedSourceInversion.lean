import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions

/-!
# Staged bounds: scoped Source inversion

Inversion and typing of scoped Source derivations, by statement form.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
/-! Actual for-header traces expose each initializer, allocation and write.
The returned context and heap remain those reached by the original item list. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
open Frontend SourceInference Staging.Recursive

variable {program : Program} {registry : Registry} {invocation : Scope}
  {context nextContext finalContext : SourceSemantics.Context}
  {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {rest : List ForItemForm} {size : Nat} {outcome : ForItemsOutcome}

theorem empty (trace : Size.ForItems program registry size invocation context environment before
    [] finalContext outcome after) :
    finalContext = context ∧ outcome = .done environment ∧ after = before := by
  cases trace
  exact ⟨rfl, rfl, rfl⟩

theorem absent {binder : TypedBinder}
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.ForItems program registry size invocation context environment before
      (.letDecl binder none :: rest) finalContext outcome after) :
    ∃ tailSize location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Size.ForItems program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  cases trace with
  | absent _ actualExtended allocated remaining =>
      cases extended
      cases actualExtended
      exact ⟨_, _, _, rfl, allocated, remaining⟩

theorem initialized {binder : TypedBinder} {initializer : ExpressionId}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.ForItems program registry size invocation context environment before
      (.letDecl binder (some initializer) :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.fault failure) after) ∨
    (∃ childSize tailSize value location middle bound,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Size.ForItems program registry tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after) := by
  cases trace with
  | initializedGeneralized _ _ polymorphic _ _ _ => exact False.elim (polymorphic monomorphic)
  | initialized _ actualExtended child allocated remaining =>
      cases extended
      cases actualExtended
      exact .inr ⟨_, _, _, _, _, _, rfl, child, allocated, remaining⟩
  | initializerFault _ child => exact .inl ⟨_, _, rfl, rfl, rfl, child⟩

theorem expression {id : ExpressionId}
    (trace : Size.ForItems program registry size invocation context environment before
      (.expression id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before id (.fault failure) after) ∨
    (∃ childSize tailSize value middle,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before id (.value value) middle ∧
      Size.ForItems program registry tailSize invocation context environment middle rest finalContext outcome after) := by
  cases trace with
  | expression child remaining => exact .inr ⟨_, _, _, _, rfl, child, remaining⟩
  | expressionFailure child => exact .inl ⟨_, _, rfl, rfl, rfl, child⟩

private theorem target_functional {heap : Dynamic.Heap} {place : PlaceResolution}
    {left right : Dynamic.ResolvedPlace}
    (first : BareTarget environment heap place left)
    (second : BareTarget environment heap place right) : left = right := by
  cases first with
  | intro _ leftLookup leftRead leftValue =>
    cases second with
    | intro _ rightLookup rightRead rightValue =>
      have locations := leftLookup.functional rightLookup
      cases locations
      have cells := leftRead.functional rightRead
      cases cells
      have values := leftValue.functional rightValue
      cases values
      rfl

theorem assignment {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Size.ForItems program registry size invocation context environment before
      (.assignValue assignment operator rhs :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize right currentCell initial currentSelected,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧
      outcome = .fault (.semantic (.invalidAssignmentOperands operator)) ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ childSize tailSize value middle written updated,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      Size.ForItems program registry tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | projectedAssignment projected _ _ _ _ _
  | projectedAssignmentRootFault projected _
  | projectedAssignmentKeysFault projected _ _
  | projectedAssignmentGetterFault projected _ _
  | projectedAssignmentRhsFault projected _ _ _
  | projectedAssignmentWriteFault projected _ _ _ _ =>
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
  | assignment actualSnapshot child write remaining =>
      have targets := target_functional snapshot actualSnapshot
      cases targets
      exact .inr (.inr ⟨_, _, _, _, _, _, rfl, child, write, remaining⟩)
  | assignmentOperands actualSnapshot child currentRead rootType initialValue pathRead invalid =>
      have targets := target_functional snapshot actualSnapshot
      cases targets
      exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, child,
        currentRead, rootType, initialValue, pathRead, invalid⟩)
  | assignmentFailure _ child => exact .inl ⟨_, _, rfl, rfl, rfl, child⟩
  | unbound _ missing =>
      cases snapshot with
      | intro _ lookup _ _ => exact False.elim (missing.excludes_lookup lookup)
  | dangling _ lookup missing =>
      cases snapshot with
      | intro _ actualLookup read _ =>
          have locations := lookup.functional actualLookup
          cases locations
          exact False.elim (missing.excludes_read read)

theorem bitNot {assignment : AssignmentResolution}
    (bare : assignment.target.projections = [])
    (trace : Size.ForItems program registry size invocation context environment before
      (.assignBitNot assignment :: rest) finalContext outcome after) :
    (∃ reason, size = Size.stepSize [] ∧ finalContext = context ∧
      outcome = .fault (.semantic reason) ∧ after = before ∧
      Dynamic.SourcePlaceBitNotFaults program context invocation.evidence invocation.source
        environment before assignment.target reason before) ∨
    (∃ tailSize target updated written,
      size = Size.stepSize [tailSize] ∧ BareTarget environment before assignment.target target ∧
      Dynamic.ResolvedPlaceWrites (fun _ replacement => Dynamic.BitNotSnapshot target.selected replacement)
        before target updated written ∧
      Size.ForItems program registry tailSize invocation context environment written rest finalContext outcome after) := by
  cases trace with
  | bitNot snapshot write remaining => exact .inr ⟨_, _, _, _, rfl, snapshot, write, remaining⟩
  | bitNotFault _ failed => exact .inl ⟨_, rfl, rfl, rfl, rfl, failed⟩
  | projectedBitNot projected _ _ _ _ | projectedBitNotRootFault projected _
  | projectedBitNotKeysFault projected _ _ | projectedBitNotGetterFault projected _ _ =>
      exact (projected bare).elim

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
/-! Original Source for typing determines each header context. Successful
initialization identifies the reached context directly from its binder receipts;
no execution preservation law or program well-formedness premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
open Frontend SourceInference Staging.Recursive
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body) : Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped
      exact ⟨control, final, _, tail⟩

theorem children {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body) :
    ∃ control loopContext postContext bodyFinal bodyFacts,
      ForItemsHaveType source control context initial loopContext ∧
      ExpressionHasType source loopContext condition .bool ∧
      StatementsHaveType source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType source control.enterLoop loopContext post postContext :=
  ProtectedStateImperativeTypedSourceSites.for_loop unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

theorem initial_context {program : Program} {registry : Registry} {invocation : Scope}
    {control : ControlContext} {context staticFinal runtimeFinal : SourceSemantics.Context}
    {environment returned : Dynamic.Environment} {before after : Dynamic.Heap}
    {items : List ForItemForm} {size : Nat}
    (typed : ForItemsHaveType invocation.source control context items staticFinal)
    (trace : Size.ForItems program registry size invocation context environment before items runtimeFinal (.done returned) after) :
    runtimeFinal = staticFinal := by
  induction size using Nat.strongRecOn generalizing context staticFinal runtimeFinal environment returned before after items with
  | ind size ih =>
    cases trace with
    | empty => cases typed; rfl
    | absent mono extended allocated next =>
      cases typed with
      | cons head tail =>
        cases head with
        | letUninitialized _ _ staticExtended =>
          cases Dynamic.BinderExtends.functional extended staticExtended
          exact ih _ (Size.child_lt_stepSize (by simp)) tail next
    | initialized mono extended child allocated next =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized _ _ _ staticExtended =>
          cases Dynamic.BinderExtends.functional extended staticExtended
          exact ih _ (Size.child_lt_stepSize (by simp)) tail next
        | letInitializedGeneralized poly _ _ _ _ => exact (poly mono).elim
    | initializedGeneralized _ _ poly extended allocated next =>
      cases typed with
      | cons head tail =>
        cases head with
        | letInitialized _ mono _ _ => exact (poly mono).elim
        | letInitializedGeneralized _ _ _ _ staticExtended =>
          cases Dynamic.BinderExtends.functional extended staticExtended
          exact ih _ (Size.child_lt_stepSize (by simp)) tail next
    | expression child next | assignment _ child _ next | bitNot _ _ next
    | projectedAssignment _ _ _ child _ next | projectedBitNot _ child _ _ next =>
      cases typed with
      | cons head tail =>
        cases head
        exact ih _ (Size.child_lt_stepSize (by simp)) tail next

theorem children_at_initial {program : Program} {registry : Registry} {invocation : Scope}
    {context loopContext : SourceSemantics.Context} {environment loopEnvironment : Dynamic.Environment}
    {before initialized : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {initial post : List ForItemForm} {condition : ExpressionId} {body : List StatementId} {size : Nat}
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : Statements invocation.source context (id :: rest))
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .forLoop initial condition post body)
    (trace : Size.ForItems program registry size invocation context environment before initial loopContext (.done loopEnvironment) initialized) :
    ∃ control postContext bodyFinal bodyFacts,
      ForItemsHaveType invocation.source control context initial loopContext ∧
      ExpressionHasType invocation.source loopContext condition .bool ∧
      StatementsHaveType invocation.source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType invocation.source control.enterLoop loopContext post postContext := by
  obtain ⟨control, staticLoop, postContext, bodyFinal, bodyFacts, initialTyped, conditionTyped, bodyTyped, postTyped⟩ :=
    children unique typed found form
  cases initial_context initialTyped trace
  exact ⟨control, postContext, bodyFinal, bodyFacts, initialTyped, conditionTyped, bodyTyped, postTyped⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForSourceInversion
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
  | letGeneralized actual same _ _ _ _ _
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
/-! A branch restores its original lexical context for the suffix. Static
stopping is applied only to the independently erased, actual arm execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
open Frontend SourceInference Staging.Recursive
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped <;> exact ⟨control, final, _, tail⟩

theorem condition {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {test : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen test thenBody elseBody) :
    ExpressionHasType source context test .bool := by
  obtain ⟨control, final, facts, head⟩ := ProtectedStateImperativeTypedSourceSites.head typed
  obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
  have same : actual = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  rw [form] at formTyped
  cases formTyped <;> assumption

theorem stopped_not_fallthrough {program : Program} {registry : Registry}
    {size : Nat} {invocation : Staging.Recursive.Scope} {context finalContext : SourceSemantics.Context}
    {environment finalEnvironment : Dynamic.Environment} {before after : Dynamic.Heap}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique invocation.source)
    (stopped : GenericLexicalStatements.Stopped invocation.source statements)
    (trace : Size.StatementsIn program registry false size invocation context environment before
      statements finalContext (.fallthrough finalEnvironment) after) : False := by
  have terminal := stopped.terminates unique false trace.sound.fallthrough_scoped
  cases terminal

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBranchSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
/-! The actual match statement retains its source-ordered selection and only the
suffix reached after fallthrough. Every child has its original strict grade. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
open Frontend SourceInference Staging.Recursive

theorem match_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ matchSize value,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.returned value) after) ∨
    (∃ matchSize failure,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.fault failure) after) ∨
    (∃ matchSize,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .breaking environment ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.breaking environment) after) ∨
    (∃ matchSize,
      size = Size.stepSize [matchSize] ∧ finalContext = context ∧ outcome = .continuing environment ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.continuing environment) after) ∨
    (∃ matchSize tailSize middle,
      size = Size.stepSize [matchSize, tailSize] ∧
      Size.Match program registry matchSize invocation context environment before
        resolution (.fallthrough environment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .matchWith resolution := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letGeneralized actual same _ _ _ _ _
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
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | matchReturned actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, matched⟩
  | matchFault actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, rfl, rfl, rfl, matched⟩)
  | matchBreaking actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inl ⟨_, rfl, rfl, rfl, matched⟩))
  | matchContinuing actual same matched =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inl ⟨_, rfl, rfl, rfl, matched⟩)))
  | matchFallthrough actual same matched next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr ⟨_, _, _, rfl, matched, next⟩)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
/-! Original Source typing supplies the actual scrutinee, ordered arm typing,
fallback and restored-context suffix. No selected branch or execution is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution) : Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped <;> exact ⟨control, final, _, tail⟩

theorem sites {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {resolution : MatchResolution} {scrutinee : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutinee) :
    ∃ control caseFacts,
      ExpressionHasType source context resolution.scrutinee scrutinee.type ∧
      MatchCasesHaveType source control context scrutinee.type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts) := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have head : ∃ middle headFacts, StatementHasType source control context id middle headFacts := by
    cases typed with
    | singleton head => exact ⟨_, _, head⟩
    | cons head _ => exact ⟨_, _, head⟩
  obtain ⟨middle, headFacts, head⟩ := head
  obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
  have same : actual = node := Option.some.inj
    ((lookupStatement?_complete unique contains).symm.trans found)
  subst actual
  rw [form] at formTyped
  have common : ∃ type caseFacts,
      ExpressionHasType source context resolution.scrutinee type ∧
      MatchCasesHaveType source control context type resolution.cases caseFacts ∧
      (∀ statements, resolution.defaultBody = some statements →
        ∃ final facts, StatementsHaveType source control context statements final facts) := by
    cases formTyped with
    | matchWithoutDefault absent scrutineeTyped casesTyped =>
        exact ⟨_, _, scrutineeTyped, casesTyped, fun statements present => by simp_all⟩
    | matchWithDefault present scrutineeTyped casesTyped defaultTyped =>
        exact ⟨_, _, scrutineeTyped, casesTyped, fun statements selected => by
          cases Option.some.inj (present.symm.trans selected)
          exact ⟨_, _, defaultTyped⟩⟩
  obtain ⟨type, caseFacts, scrutineeTyped, casesTyped, defaults⟩ := common
  obtain ⟨stored, storedContains, sameType⟩ := scrutineeTyped.stored_type
  have sameNode : stored = scrutinee := Option.some.inj
    ((lookupExpression?_complete unique storedContains).symm.trans scrutineeFound)
  subst stored
  exact ⟨control, caseFacts, sameType ▸ scrutineeTyped, sameType ▸ casesTyped, defaults⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedMatchSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
/-! The actual block retains its scoped body and only the suffix reached after
fallthrough. Lexical bindings are restored; the reached heap is retained. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
open Frontend SourceInference Staging.Recursive

theorem block_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .block statements)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ innerSize innerContext value,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .returned value ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.returned value) after) ∨
    (∃ innerSize innerContext failure,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.fault failure) after) ∨
    (∃ innerSize innerContext innerEnvironment,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .breaking environment ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.breaking innerEnvironment) after) ∨
    (∃ innerSize innerContext innerEnvironment,
      size = Size.stepSize [innerSize] ∧ finalContext = context ∧ outcome = .continuing environment ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.continuing innerEnvironment) after) ∨
    (∃ innerSize tailSize innerContext innerEnvironment middle,
      size = Size.stepSize [innerSize, tailSize] ∧
      Size.StatementsIn program registry false innerSize invocation context environment before
        statements innerContext (.fallthrough innerEnvironment) middle ∧
      Size.StatementsIn program registry mode tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape {other : StatementNode} (contains : ContainsStatement invocation.source id other) :
      other.form = .block statements := by
    have same := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
    subst other
    exact form
  cases trace with
  | breaking actual same | continuing actual same
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letGeneralized actual same _ _ _ _ _
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
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | blockReturned actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, _, rfl, rfl, rfl, inner⟩
  | blockFault actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩)
  | blockBreaking actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩))
  | blockContinuing actual same inner =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inl ⟨_, _, _, rfl, rfl, rfl, inner⟩)))
  | blockFallthrough actual same inner next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr ⟨_, _, _, _, _, rfl, inner, next⟩)))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
/-! Original Source typing supplies the scoped block body and suffix at the
same entry context. No execution or result is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) :
    Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped
      exact ⟨control, final, _, tail⟩

theorem inner {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .block statements) :
    Statements source context statements :=
  ProtectedStateImperativeTypedSourceSites.block_typed unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBlockSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceInversion
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
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockBreaking actual same _ | blockContinuing actual same _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letGeneralized actual same _ _ _ _ _
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
/-! Original Source typing supplies the condition, scoped body and suffix at
the same outer context. No loop execution or result is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
open Frontend SourceInference
open ProtectedStateImperativeTypedSourceSites (Statements)

theorem suffix {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements) :
    Statements source context rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, context, _, .nil _ _⟩
  | cons head tail =>
      obtain ⟨actual, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping head
      have same : actual = node := Option.some.inj
        ((lookupStatement?_complete unique contains).symm.trans found)
      subst actual
      rw [form] at formTyped
      cases formTyped
      exact ⟨control, final, _, tail⟩

theorem children {source : TypedSource} {context : SourceSemantics.Context}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {condition : ExpressionId} {statements : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (typed : Statements source context (id :: rest))
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition statements) :
    ExpressionHasType source context condition .bool ∧ Statements source context statements :=
  ProtectedStateImperativeTypedSourceSites.while_loop unique
    (ProtectedStateImperativeTypedSourceSites.head typed) found form

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedWhileSourceTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
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
    (∃ testSize branchSize truth innerEnvironment middle innerContext,
      size = Size.stepSize [testSize, branchSize] ∧ finalContext = context ∧ outcome = .breaking environment ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.value (.bool truth)) middle ∧
      Size.StatementsIn program registry false branchSize invocation context environment middle
        (if truth then thenBody else elseBody.getD []) innerContext (.breaking innerEnvironment) after) ∨
    (∃ testSize branchSize truth innerEnvironment middle innerContext,
      size = Size.stepSize [testSize, branchSize] ∧ finalContext = context ∧ outcome = .continuing environment ∧
      Size.Expression program registry testSize invocation context environment before
        condition (.value (.bool truth)) middle ∧
      Size.StatementsIn program registry false branchSize invocation context environment middle
        (if truth then thenBody else elseBody.getD []) innerContext (.continuing innerEnvironment) after) ∨
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
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | matchBreaking actual same _ | matchContinuing actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | returnUnit actual same | returnValue actual same _ | returnFault actual same _
  | tail actual same _ | discard actual same _ _ | discardValue actual same _ _ | expressionFault actual same _
  | letGeneralized actual same _ _ _ _ _
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
  | ifBreaking actual same test branch =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, test, branch⟩)))
  | ifContinuing actual same test branch =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, _, _, _, rfl, rfl, rfl, test, branch⟩))))
  | ifFallthrough actual same test branch next =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inr (.inr (.inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, rfl, test, branch, next⟩))))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedConditionalSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
/-! Actual lexical Source steps expose the initializer and the allocated tail.
The tail keeps its extended context and final context; no body execution law
or chosen allocation is supplied separately. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
open Frontend SourceInference Staging.Recursive

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (found : source.lookupStatement? id = some node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj ((lookupStatement?_complete unique present).symm.trans found)
  cases nodeEq
  exact same

private theorem extension_unique {owner : Resolved.DeclarationId}
    {context first second : SourceSemantics.Context} {binder : TypedBinder}
    (left : BinderExtends owner context binder first)
    (right : BinderExtends owner context binder second) : first = second := by
  cases left
  cases right
  rfl

theorem absent {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder none)
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    ∃ tailSize location bound,
      size = Size.stepSize [tailSize] ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Size.StatementsIn program registry mode tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
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
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
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
  | letInitialized actual same _ _ _ _ _ | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letUninitialized actual same _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact ⟨_, _, _, rfl, allocated, remaining⟩

theorem initialized {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context nextContext finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {binder : TypedBinder} {initializer : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .letDecl binder (some initializer))
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.fault failure) after) ∨
    (∃ childSize tailSize value location middle bound,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Size.StatementsIn program registry mode tailSize invocation nextContext
        ((binder.id, location) :: environment) bound rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ polymorphic _ _ _ =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact False.elim (polymorphic monomorphic)
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
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
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
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
  | letUninitialized actual same _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | letInitialized actual same child _ actualExtended allocated remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have contexts := extension_unique extended actualExtended
      cases contexts
      exact .inr ⟨_, _, _, _, _, _, rfl, child, allocated, remaining⟩
  | letFault actual same _ child =>
      have equal := (shape actual).symm.trans same
      cases equal
      exact .inl ⟨_, _, rfl, rfl, rfl, child⟩

theorem return_unit {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {rest : List StatementId} {node : StatementNode}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .returnStmt none)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    finalContext = context ∧ outcome = .returned .unit ∧ after = before := by
  have shape := @statement_shape _ _ _ _ unique found form
  cases trace with
  | letGeneralized actual same _ _ _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | breaking actual same | continuing actual same =>
      cases (shape actual).symm.trans same
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
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | returnUnit actual same => exact ⟨rfl, rfl, rfl⟩
  | returnValue actual same _ | returnFault actual same _
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
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedLexicalSourceInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedBitNotSourceInversion
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
  | letGeneralized actual same _ _ _ _ _
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedProjectedAssignmentSourceInversion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareBitNotSourceInversion
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
/-! A supported terminal Head selects the actual expression child of a
staged Source statement trace. The real Source grade and both failure tags
are retained before applying the strict expression induction hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedScopedTerminalStatements (Head control)

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

/-- Neither a completed body law nor a separate child trace is an input.
The literal Source constructor selects its one used child. -/
theorem child_of_body {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {expression : ExpressionId} {statements : List StatementId}
    {size : Nat} {bodyOutcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (head : Head invocation expression mode statements)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      statements finalContext bodyOutcome after) :
    ∃ childSize outcome,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ bodyOutcome = control outcome ∧
      Size.Expression program registry childSize invocation context environment before
        expression outcome after := by
  cases head with
  | returning rest contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual same | continuing actual same =>
        cases (shape actual).symm.trans same
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchBreaking actual form _ | matchContinuing actual form _
  | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockBreaking actual form _ | blockContinuing actual form _
  | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifBreaking actual form _ _ | ifContinuing actual form _ _
  | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | discardValue actual form child next
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | letGeneralized actual form _ _ _ _ _
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same
  | tail contains form =>
    have shape := @statement_shape _ _ _ _ unique contains form
    cases trace with
    | breaking actual same | continuing actual same =>
        cases (shape actual).symm.trans same
    | forInitializerFault actual form _ | forReturned actual form _ _ | forFault actual form _ _
    | forFallthrough actual form _ _ _
    | matchBreaking actual form _ | matchContinuing actual form _
  | matchReturned actual form _ | matchFault actual form _ | matchFallthrough actual form _ _
    | blockBreaking actual form _ | blockContinuing actual form _
  | blockReturned actual form _ | blockFault actual form _ | blockFallthrough actual form _ _
    | whileReturned actual form _ | whileFault actual form _ | whileFallthrough actual form _ _
    | ifConditionFault actual form _ | ifBreaking actual form _ _ | ifContinuing actual form _ _
  | ifReturned actual form _ _ | ifFault actual form _ _
    | ifFallthrough actual form _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnUnit actual form =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnValue actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | returnFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
    | tail actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | discard actual form child next =>
      have same := shape actual
      rw [form] at same
      cases same
    | expressionFault actual form child =>
      have same := shape actual
      rw [form] at same
      cases same
      exact ⟨_, _, rfl, rfl, rfl, child⟩
    | letGeneralized actual form _ _ _ _ _
    | letUninitialized actual form mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letInitialized actual form child mono extension allocated next =>
      have same := shape actual
      rw [form] at same
      cases same
    | letFault actual form mono child =>
      have same := shape actual
      rw [form] at same
      cases same
    | bitNotProjected actual form _ _ _ _ _
    | bitNotProjectedRootFault actual form _ _
    | bitNotProjectedKeysFault actual form _ _ _
    | bitNotProjectedGetterFault actual form _ _ _
    | bitNotBare actual form _ _ _ | bitNotBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignProjected actual form _ _ _ _ _ _
    | assignProjectedRootFault actual form _ _
    | assignProjectedKeysFault actual form _ _ _
    | assignProjectedGetterFault actual form _ _ _
    | assignProjectedRhsFault actual form _ _ _ _
    | assignProjectedWriteFault actual form _ _ _ _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBare actual form snapshot child write next =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareOperands actual form _ _ _ _ _ _ _ | assignBareFault actual form _ _ =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareUnbound actual form bare missing =>
      have same := shape actual
      rw [form] at same
      cases same
    | assignBareDangling actual form bare lookup missing =>
      have same := shape actual
      rw [form] at same
      cases same

/-- A terminal body propagates the exact Source expression outcome. -/
theorem result_of_control {type : TypeSystem.Ty} {child result : Outcome}
    (matched : BodyResult type (control child) result) : result = child := by
  cases child <;> cases matched <;> rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedTerminalSourceBodyInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedDiscardSourceBodyInversion
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
  | letGeneralized actual same _ _ _ _ _
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedBareAssignmentSourceInversion
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

/-- The actual Source rule retains RHS failure, operand rejection after a
successful RHS, or the genuine write and suffix. The target snapshot is fixed. -/
theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize right currentCell initial currentSelected,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧
      outcome = .fault (.semantic (.invalidAssignmentOperands operator)) ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ childSize tailSize value middle written updated,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      Size.StatementsIn program registry mode tailSize invocation context environment written rest finalContext outcome after) := by
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
  | assignProjected actual same projected _ _ _ _ _
  | assignProjectedRootFault actual same projected _
  | assignProjectedKeysFault actual same projected _ _
  | assignProjectedGetterFault actual same projected _ _
  | assignProjectedRhsFault actual same projected _ _ _
  | assignProjectedWriteFault actual same projected _ _ _ _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (projected empty).elim
  | assignBare actual same actualSnapshot child write remaining =>
      have equal := (shape actual).symm.trans same
      cases equal
      have targetEq := target_functional snapshot actualSnapshot
      cases targetEq
      exact .inr (.inr ⟨_, _, _, _, _, _, rfl, child, write, remaining⟩)
  | assignBareOperands actual same actualSnapshot child currentRead rootType initialValue pathRead invalid =>
      have equal := (shape actual).symm.trans same
      cases equal
      have targetEq := target_functional snapshot actualSnapshot
      cases targetEq
      exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, rfl, child,
        currentRead, rootType, initialValue, pathRead, invalid⟩)
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
end
