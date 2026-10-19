import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForHeadContracts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion

/-! A compiler initializer prefix contributes its actual item trace to the
same finite for head. Binder scopes restore only lexical bindings; all grades,
heap effects and both failure tags remain those of the executed prefix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
open Frontend SourceInference Staging.Recursive
open CallableIndexedOwnedAdmittedStagedForHeadContracts

variable {program : Program} {stages : Registry} {invocation : Scope}
  {context nextContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before middle bound written after : Dynamic.Heap} {items post : List ForItemForm}
  {test : ExpressionId} {body : List StatementId} {size childSize : Nat} {outcome : BodyOutcome}

private theorem restore_twice (outcome : BodyOutcome) (inner outer : Dynamic.Environment) :
    (outcome.restore inner).restore outer = outcome.restore outer := by
  cases outcome <;> rfl

private theorem grade_absent (initial loop : Nat) :
    Size.stepSize [Size.stepSize [initial], loop] = Size.stepSize [Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

private theorem grade_prefix (child initial loop : Nat) :
    Size.stepSize [Size.stepSize [child, initial], loop] = Size.stepSize [child, Size.stepSize [initial, loop]] := by
  simp [Size.stepSize]
  omega

/-- An actual uninitialized header allocation remains live through the rest
of initialization and the loop; the whole head restores the outer bindings. -/
theorem prepend_absent {binder : TypedBinder} {location : Dynamic.Location}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (allocated : Dynamic.Heap.Allocates before binder.scheme.body none location bound)
    (next : Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
      items test post body size outcome after) :
    Trace program stages invocation context environment before (.letDecl binder none :: items) test post body
      (Size.stepSize [size]) (outcome.restore environment) after := by
  cases next with
  | initializerFault initial => exact .initializerFault (.absent mono extended allocated initial)
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initial loop =>
      simpa only [grade_absent, restore_twice] using
        (Trace.loop (Size.ForItems.absent mono extended allocated initial) loop)

theorem prepend_initialized {binder : TypedBinder} {initializer : ExpressionId}
    {value : Dynamic.Value} {location : Dynamic.Location}
    (mono : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (child : Size.Expression program stages childSize invocation context environment before initializer (.value value) middle)
    (allocated : Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound)
    (next : Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
      items test post body size outcome after) :
    Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body
      (Size.stepSize [childSize, size]) (outcome.restore environment) after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.initialized mono extended child allocated initial))
  | @loop initialSize loopSize loopContext loopEnvironment initialized result _ initial loop =>
      simpa only [grade_prefix, restore_twice] using
        (Trace.loop (Size.ForItems.initialized mono extended child allocated initial) loop)

theorem prepend_expression {id : ExpressionId} {value : Dynamic.Value}
    (child : Size.Expression program stages childSize invocation context environment before id (.value value) middle)
    (next : Trace program stages invocation context environment middle items test post body size outcome after) :
    Trace program stages invocation context environment before (.expression id :: items) test post body
      (Size.stepSize [childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.expression child initial))
  | loop initial loop => simpa only [grade_prefix] using (Trace.loop (Size.ForItems.expression child initial) loop)

theorem prepend_assignment {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {value updated : Dynamic.Value} {target : Dynamic.ResolvedPlace}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.value value) middle)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
      middle target updated written)
    (next : Trace program stages invocation context environment written items test post body size outcome after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [childSize, size]) outcome after := by
  cases next with
  | initializerFault initial =>
      simpa only [BodyOutcome.restore, Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc, Nat.add_comm 1] using
        (Trace.initializerFault (Size.ForItems.assignment snapshot child write initial))
  | loop initial loop => simpa only [grade_prefix] using (Trace.loop (Size.ForItems.assignment snapshot child write initial) loop)

theorem initializer_fault {binder : TypedBinder} {initializer : ExpressionId} {failure : Failure}
    (mono : binder.scheme.quantified = [])
    (child : Size.Expression program stages childSize invocation context environment before initializer (.fault failure) after) :
    Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.initializerFault mono child)

theorem expression_fault {id : ExpressionId} {failure : Failure}
    (child : Size.Expression program stages childSize invocation context environment before id (.fault failure) after) :
    Trace program stages invocation context environment before (.expression id :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.expressionFailure child)

theorem assignment_fault {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {failure : Failure}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.fault failure) after) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault failure) after :=
  .initializerFault (.assignmentFailure snapshot child)

theorem assignment_operands {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {target : Dynamic.ResolvedPlace} {right : Dynamic.Value} {currentCell : Dynamic.Cell}
    {initial currentSelected : Option Dynamic.Value}
    (snapshot : BareTarget environment before assignment.target target)
    (child : Size.Expression program stages childSize invocation context environment before rhs (.value right) after)
    (currentRead : Dynamic.Heap.Reads after target.location currentCell)
    (rootType : currentCell.type = target.rootType)
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (pathRead : Dynamic.ProjectionsRead initial target.projections currentSelected)
    (invalid : Dynamic.AssignmentOperandsInvalid operator target.selected right) :
    Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body
      (Size.stepSize [Size.stepSize [childSize]]) (.fault (.semantic (.invalidAssignmentOperands operator))) after :=
  .initializerFault (.assignmentOperands snapshot child currentRead rootType initialValue pathRead invalid)

/-- Empty initialization contributes its genuine empty-items grade. -/
theorem nil
    (trace : Trace program stages invocation context environment before [] test post body size outcome after) :
    ∃ loopSize rawOutcome,
      size = Size.stepSize [Size.stepSize [], loopSize] ∧ outcome = rawOutcome.restore environment ∧
      Size.ForLoop program stages loopSize invocation context environment before test post body rawOutcome after := by
  cases trace with
  | initializerFault initial => cases initial
  | loop initial loop =>
      cases initial
      exact ⟨_, _, rfl, rfl, loop⟩

theorem absent {binder : TypedBinder}
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Trace program stages invocation context environment before (.letDecl binder none :: items) test post body size outcome after) :
    ∃ nextSize location bound nextOutcome,
      size = Size.stepSize [nextSize] ∧ outcome = nextOutcome.restore environment ∧
      Dynamic.Heap.Allocates before binder.scheme.body none location bound ∧
      Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
        items test post body nextSize nextOutcome after := by
  cases trace with
  | initializerFault initial =>
      obtain ⟨tailSize, location, bound, rfl, allocated, next⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended initial
      exact ⟨_, location, bound, _, rfl, rfl, allocated, .initializerFault next⟩
  | loop initial loop =>
      obtain ⟨tailSize, location, bound, rfl, allocated, next⟩ :=
        CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.absent extended initial
      exact ⟨_, location, bound, _, grade_absent _ _, (restore_twice _ _ _).symm, allocated, .loop next loop⟩

theorem initialized {binder : TypedBinder} {initializer : ExpressionId}
    (monomorphic : binder.scheme.quantified = [])
    (extended : BinderExtends invocation.source.owner context binder nextContext)
    (trace : Trace program stages invocation context environment before (.letDecl binder (some initializer) :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before initializer (.fault failure) after) ∨
    (∃ childSize nextSize value location middle bound nextOutcome,
      size = Size.stepSize [childSize, nextSize] ∧ outcome = nextOutcome.restore environment ∧
      Size.Expression program stages childSize invocation context environment before initializer (.value value) middle ∧
      Dynamic.Heap.Allocates middle binder.scheme.body (some value) location bound ∧
      Trace program stages invocation nextContext ((binder.id, location) :: environment) bound
        items test post body nextSize nextOutcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized monomorphic extended initial with failed | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, tailSize, value, location, middle, bound, rfl, child, allocated, next⟩ := continued
        refine .inr ⟨_, _, _, _, _, _, _, ?_, rfl, child, allocated, .initializerFault next⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.initialized monomorphic extended initial with failed | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨childSize, tailSize, value, location, middle, bound, rfl, child, allocated, next⟩ := continued
        exact .inr ⟨_, _, _, _, _, _, _, grade_prefix _ _ _, (restore_twice _ _ _).symm,
          child, allocated, .loop next loop⟩

theorem expression {id : ExpressionId}
    (trace : Trace program stages invocation context environment before (.expression id :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before id (.fault failure) after) ∨
    (∃ childSize nextSize value middle,
      size = Size.stepSize [childSize, nextSize] ∧
      Size.Expression program stages childSize invocation context environment before id (.value value) middle ∧
      Trace program stages invocation context environment middle items test post body nextSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression initial with failed | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, tailSize, value, middle, rfl, child, next⟩ := continued
        refine .inr ⟨_, _, _, _, ?_, child, .initializerFault next⟩
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.expression initial with failed | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨childSize, tailSize, value, middle, rfl, child, next⟩ := continued
        exact .inr ⟨_, _, _, _, grade_prefix _ _ _, child, .loop next loop⟩

theorem assignment {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId} {target : Dynamic.ResolvedPlace}
    (snapshot : BareTarget environment before assignment.target target)
    (trace : Trace program stages invocation context environment before (.assignValue assignment operator rhs :: items) test post body size outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [Size.stepSize [childSize]] ∧ outcome = .fault failure ∧
      Size.Expression program stages childSize invocation context environment before rhs (.fault failure) after) ∨
    (∃ childSize right currentCell initial currentSelected,
      size = Size.stepSize [Size.stepSize [childSize]] ∧
      outcome = .fault (.semantic (.invalidAssignmentOperands operator)) ∧
      Size.Expression program stages childSize invocation context environment before rhs (.value right) after ∧
      Dynamic.Heap.Reads after target.location currentCell ∧ currentCell.type = target.rootType ∧
      Dynamic.RootInitialValue currentCell initial ∧ Dynamic.ProjectionsRead initial target.projections currentSelected ∧
      Dynamic.AssignmentOperandsInvalid operator target.selected right) ∨
    (∃ childSize nextSize value middle written updated,
      size = Size.stepSize [childSize, nextSize] ∧
      Size.Expression program stages childSize invocation context environment before rhs (.value value) middle ∧
      Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.AssignmentValueApplies operator target.selected value replacement)
        middle target updated written ∧
      Trace program stages invocation context environment written items test post body nextSize outcome after) := by
  cases trace with
  | initializerFault initial =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot initial with failed | invalid | continued
      · obtain ⟨childSize, failure, rfl, _, same, child⟩ := failed
        cases same
        exact .inl ⟨_, _, rfl, rfl, child⟩
      · obtain ⟨childSize, right, currentCell, initial, currentSelected, rfl, _, same,
          child, currentRead, rootType, initialValue, pathRead, operands⟩ := invalid
        cases same
        exact .inr (.inl ⟨_, _, _, _, _, rfl, rfl, child, currentRead, rootType, initialValue, pathRead, operands⟩)
      · obtain ⟨childSize, tailSize, value, middle, written, updated, rfl, child, write, next⟩ := continued
        refine .inr (.inr ⟨_, _, _, _, _, _, ?_, child, write, .initializerFault next⟩)
        simp only [Size.stepSize, List.sum_cons, List.sum_nil, Nat.add_zero]
        omega
  | loop initial loop =>
      rcases CallableIndexedOwnedPreparedStagedScopedForItemsSourceInversion.assignment snapshot initial with failed | invalid | continued
      · obtain ⟨_, _, _, _, same, _⟩ := failed
        cases same
      · obtain ⟨_, _, _, _, _, _, _, same, _⟩ := invalid
        cases same
      · obtain ⟨childSize, tailSize, value, middle, written, updated, rfl, child, write, next⟩ := continued
        exact .inr (.inr ⟨_, _, _, _, _, _, grade_prefix _ _ _, child, write, .loop next loop⟩)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedForInitializerSource
