import Solcore.SourceSemantics.Staging.RecursiveTraceSize

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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion
