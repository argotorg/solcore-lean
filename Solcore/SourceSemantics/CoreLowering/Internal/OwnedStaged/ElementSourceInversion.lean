import Solcore.SourceSemantics.Staging.Internal.TraceSize
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateForHeaders
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericLexical
import Solcore.SourceSemantics.Staging.Erasure
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedExpressions

/-!
# Staged inversions of writes to an element

A sized Source trace of an assignment, or of an in-place `~`, at an element place, inverted into the
cases a head takes: the root's or a leading key's fault, the element target's fault, the right side's or
the operand's fault, the write's fault, and the write with the tail; and the sized `ElementTarget` of one
element, resolved or faulting. Main declarations: `ElementAssignmentSourceInversion.child_and_tail`,
`single_resolved`, `single_fault` and `ElementBitNotSourceInversion.child_and_tail`.
-/

section
/-! An assignment at an element place runs `assignElement` and its faults, or faults at the root
or a leading key by the projected rules, which only require some projection. The other projected
rules take a getter snapshot, whose `Values` has no element case, and the bare rules take no
projection. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ElementAssignmentSourceInversion
open Frontend SourceInference Staging.Recursive

theorem values_element_free {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List Dynamic.EvaluatedProjection} (ordered : ProjectedTarget.Values projections values evaluated) :
    ∀ index, PlaceProjection.element index ∉ projections := by
  induction ordered with
  | nil => intro index member; cases member
  | member _ ih =>
      intro index member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
      · exact ih index member
  | index _ ih =>
      intro index member
      rcases List.mem_cons.mp member with equal | member
      · cases equal
      · exact ih index member

theorem values_absurd {projections : List PlaceProjection} {values : List Dynamic.Value}
    {evaluated : List Dynamic.EvaluatedProjection} (element : ElementPlace projections)
    (ordered : ProjectedTarget.Values projections values evaluated) : False := by
  obtain ⟨index, member⟩ := element.mem
  exact values_element_free ordered index member

/-- No getter snapshot is taken at an element place. -/
theorem snapshot_absurd {environment : Dynamic.Environment} {before after : Dynamic.Heap} {place : PlaceResolution}
    {values : List Dynamic.Value} {target : Dynamic.ResolvedPlace} (element : ElementPlace place.projections)
    (snapshot : ProjectedTarget.Snapshot environment before after place values target) : False := by
  cases snapshot with
  | intro _ _ ordered _ _ _ => exact values_absurd element ordered

/-- No getter faults at an element place. -/
theorem getterFault_absurd {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {values : List Dynamic.Value} {reason : Dynamic.SemanticFault}
    (element : ElementPlace place.projections)
    (failed : ProjectedTarget.GetterFault environment before after place values reason) : False := by
  cases failed with
  | dangling _ _ ordered _ | projection _ _ ordered _ _ _ | uninitialized _ _ ordered _ _ _ _ =>
      exact values_absurd element ordered

inductive Result (program : Program) (registry : Registry) (mode : Bool) (invocation : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (rest : List StatementId) :
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
  | targetFault {targetSize failure after}
      (failed : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.fault failure) after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [targetSize]) context (.fault failure) after
  | rhsFault {targetSize childSize target targetHeap failure after}
      (resolved : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.resolved target) targetHeap)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs
        (.fault failure) after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [targetSize, childSize]) context (.fault failure) after
  | writeFault {targetSize childSize target targetHeap right reason after}
      (resolved : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.resolved target) targetHeap)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs
        (.value right) after)
      (failed : ProjectedTarget.WriteFault operator target right after reason) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [targetSize, childSize]) context (.fault (.semantic reason)) after
  | success {targetSize childSize tailSize target targetHeap right middle updated written finalContext outcome after}
      (resolved : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.resolved target) targetHeap)
      (child : Size.Expression program registry childSize invocation context environment targetHeap rhs
        (.value right) middle)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement =>
          Dynamic.CompoundAssignmentApplies assignment.target.type operator target.selected right replacement)
        middle target updated written)
      (next : Size.StatementsIn program registry mode tailSize invocation context environment written rest
        finalContext outcome after) :
      Result program registry mode invocation context environment before assignment operator rhs rest
        (Size.stepSize [targetSize, childSize, tailSize]) finalContext outcome after

theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp}
    {rhs : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs)
    (element : ElementPlace assignment.target.projections)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    Result program registry mode invocation context environment before assignment operator rhs rest size
      finalContext outcome after := by
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
  | bitNotElement actual same _ _ _ _
  | bitNotElementTargetFault actual same _ _
  | bitNotElementOperandFault actual same _ _ _ _
  | bitNotProjectedOperandFault actual same _ _ _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | letFault actual same _ _ =>
      have impossible := (shape actual).symm.trans same
      cases impossible
  | assignBare actual same snapshot _ _ _
  | assignBareOperands actual same snapshot _ _ _ _ _ _
  | assignBarePanic actual same snapshot _ _ _ _ _ _
  | assignBareFault actual same snapshot _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (element.ne_nil empty).elim
  | assignBareUnbound actual same empty _
  | assignBareDangling actual same empty _ _ =>
      cases (shape actual).symm.trans same
      exact (element.ne_nil empty).elim
  | assignProjected actual same _ _ snapshot _ _ _
  | assignProjectedRhsFault actual same _ _ snapshot _
  | assignProjectedWriteFault actual same _ _ snapshot _ _ =>
      cases (shape actual).symm.trans same
      exact (snapshot_absurd element snapshot).elim
  | assignProjectedGetterFault actual same _ _ failed =>
      cases (shape actual).symm.trans same
      exact (getterFault_absurd element failed).elim
  | assignProjectedRootFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .rootFault failed
  | assignProjectedKeysFault actual same _ ready keys =>
      cases (shape actual).symm.trans same
      exact .keysFault ready keys
  | assignElement actual same _ resolved child write next =>
      cases (shape actual).symm.trans same
      exact .success resolved child write next
  | assignElementTargetFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .targetFault failed
  | assignElementRhsFault actual same _ resolved child =>
      cases (shape actual).symm.trans same
      exact .rhsFault resolved child
  | assignElementWriteFault actual same _ resolved child failed =>
      cases (shape actual).symm.trans same
      exact .writeFault resolved child failed

theorem nil_ne_append_element {leading : List PlaceProjection} {index : ExpressionId} :
    ([] : List PlaceProjection) ≠ leading ++ [.element index] := by
  simp

/-- One element is the last projection with nothing leading it. -/
theorem single_split {key index : ExpressionId} {leading : List PlaceProjection}
    (equal : [PlaceProjection.element key] = leading ++ [.element index]) : leading = [] ∧ index = key := by
  cases leading with
  | nil =>
      simp at equal
      exact ⟨rfl, equal.symm⟩
  | cons head tail =>
      simp at equal

/-- The place of no projection resolves only by `elementRoot`. -/
theorem bare_resolved {program : Program} {registry : Registry} {size : Nat} {scope : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace} (bare : place.projections = [])
    (trace : Size.ElementTarget program registry size scope context environment before place (.resolved target)
      after) :
    size = Size.stepSize [] ∧ after = before ∧
      ∃ location cell initial, Dynamic.Environment.LooksUp environment place.root location ∧
        Dynamic.Heap.Reads before location cell ∧ Dynamic.RootInitialValue cell initial ∧
        target =
          { location := location, rootType := cell.type, valueType := place.type, projections := [],
            selected := initial } := by
  cases trace with
  | elementRoot _ lookup read initialValue => exact ⟨rfl, rfl, _, _, _, lookup, read, initialValue, rfl⟩
  | elementStep projections_eq _ _ _ _ _ _ =>
      exact (nil_ne_append_element (bare.symm.trans projections_eq)).elim

/-- The place of no projection faults only by `elementRootFault`. -/
theorem bare_fault {program : Program} {registry : Registry} {size : Nat} {scope : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {failure : Failure} (bare : place.projections = [])
    (trace : Size.ElementTarget program registry size scope context environment before place (.fault failure)
      after) :
    size = Size.stepSize [] ∧ after = before ∧
      ∃ reason, failure = .semantic reason ∧ ProjectedTarget.RootFault environment before place reason := by
  cases trace with
  | elementRootFault _ failed => exact ⟨rfl, rfl, _, rfl, failed⟩
  | elementPrefixFault projections_eq _ | elementUninitialized projections_eq _ _
  | elementIndexFault projections_eq _ _ _ | elementIndexType projections_eq _ _ _ _ _
  | elementOutOfBounds projections_eq _ _ _ _ _ _ =>
      exact (nil_ne_append_element (bare.symm.trans projections_eq)).elim

/-- The place `root[key]` of one element resolved: the bare root's lookup and read, whose value is
an array's reference, the key's word, and the array's own cell, whose element at the word is the
snapshot. -/
inductive SingleResolved (program : Program) (registry : Registry) (scope : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (place : PlaceResolution) (key : ExpressionId) : Nat → Dynamic.ResolvedPlace → Dynamic.Heap → Prop where
  | intro {indexSize location cell element arrayLocation position after arrayCell elements selected}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (read : Dynamic.Heap.Reads before location cell)
      (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
      (indexed : Size.Expression program registry indexSize scope context environment before key
        (.value (.word position)) after)
      (arrayRead : Dynamic.Heap.Reads after arrayLocation arrayCell)
      (arrayValue : Dynamic.RootInitialValue arrayCell (some (.arrayObject element elements)))
      (selection : Dynamic.ValueAt elements position.val selected) :
      SingleResolved program registry scope context environment before place key
        (Size.stepSize [Size.stepSize [], indexSize])
        { location := arrayLocation, rootType := arrayCell.type, valueType := place.type,
          projections := [.element position.val], selected := some selected }
        after

/-- The faults of the place `root[key]` of one element, each at its size: the bare root's, a root not
yet initialized, the key's and a key that is not a word at a root that holds a value, and `0x32` from the
array's length on. -/
inductive SingleFault (program : Program) (registry : Registry) (scope : Scope)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (place : PlaceResolution) (key : ExpressionId) : Nat → Failure → Dynamic.Heap → Prop where
  | root {reason}
      (failed : ProjectedTarget.RootFault environment before place reason) :
      SingleFault program registry scope context environment before place key
        (Size.stepSize [Size.stepSize []]) (.semantic reason) before
  | uninitialized {location cell}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (read : Dynamic.Heap.Reads before location cell)
      (initialValue : Dynamic.RootInitialValue cell none) :
      SingleFault program registry scope context environment before place key
        (Size.stepSize [Size.stepSize []]) (.semantic (.uninitializedLocation location)) before
  | index {indexSize location cell rootValue failure after}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (read : Dynamic.Heap.Reads before location cell)
      (initialValue : Dynamic.RootInitialValue cell (some rootValue))
      (indexed : Size.Expression program registry indexSize scope context environment before key
        (.fault failure) after) :
      SingleFault program registry scope context environment before place key
        (Size.stepSize [Size.stepSize [], indexSize]) failure after
  | indexType {indexSize location cell rootValue value actual after}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (read : Dynamic.Heap.Reads before location cell)
      (initialValue : Dynamic.RootInitialValue cell (some rootValue))
      (indexed : Size.Expression program registry indexSize scope context environment before key
        (.value value) after)
      (not_word : ¬ Dynamic.WordValue value) (actual_type : Dynamic.ValueRuntimeType value actual) :
      SingleFault program registry scope context environment before place key
        (Size.stepSize [Size.stepSize [], indexSize]) (.semantic (.typeMismatch .word actual)) after
  | outOfBounds {indexSize location cell element arrayLocation position after arrayCell elements}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (read : Dynamic.Heap.Reads before location cell)
      (initialValue : Dynamic.RootInitialValue cell (some (.arrayRef element arrayLocation)))
      (indexed : Size.Expression program registry indexSize scope context environment before key
        (.value (.word position)) after)
      (arrayRead : Dynamic.Heap.Reads after arrayLocation arrayCell)
      (stored : arrayCell.value = some (.arrayObject element elements))
      (out_of_bounds : elements.length ≤ position.val) :
      SingleFault program registry scope context environment before place key
        (Size.stepSize [Size.stepSize [], indexSize]) (.semantic (.panic 0x32)) after

theorem single_resolved {program : Program} {registry : Registry} {size : Nat} {scope : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {key : ExpressionId} {target : Dynamic.ResolvedPlace}
    (single : place.projections = [.element key])
    (trace : Size.ElementTarget program registry size scope context environment before place (.resolved target)
      after) :
    SingleResolved program registry scope context environment before place key size target after := by
  cases trace with
  | elementRoot bare _ _ _ => cases single.symm.trans bare
  | elementStep projections_eq leadingTarget prefix_selected indexed arrayRead arrayValue selection =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, location, cell, initial, lookup, read, initialValue, rfl⟩ :=
        bare_resolved rfl leadingTarget
      have selected_eq : initial = _ := prefix_selected
      subst selected_eq
      exact .intro lookup read initialValue indexed arrayRead arrayValue selection

theorem single_fault {program : Program} {registry : Registry} {size : Nat} {scope : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {key : ExpressionId} {failure : Failure}
    (single : place.projections = [.element key])
    (trace : Size.ElementTarget program registry size scope context environment before place (.fault failure)
      after) :
    SingleFault program registry scope context environment before place key size failure after := by
  cases trace with
  | elementRootFault bare _ => cases single.symm.trans bare
  | elementPrefixFault projections_eq leadingTarget =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, reason, rfl, failed⟩ := bare_fault rfl leadingTarget
      cases failed with
      | unbound missing => exact .root (.unbound missing)
      | dangling lookup missing => exact .root (.dangling lookup missing)
  | elementUninitialized projections_eq leadingTarget prefix_empty =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, location, cell, initial, lookup, read, initialValue, rfl⟩ :=
        bare_resolved rfl leadingTarget
      have empty : initial = none := prefix_empty
      subst empty
      exact .uninitialized lookup read initialValue
  | elementIndexFault projections_eq leadingTarget prefix_initialized indexed =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, location, cell, initial, lookup, read, initialValue, rfl⟩ :=
        bare_resolved rfl leadingTarget
      have initialized : initial ≠ none := prefix_initialized
      cases initial with
      | none => exact absurd rfl initialized
      | some _ => exact .index lookup read initialValue indexed
  | elementIndexType projections_eq leadingTarget prefix_initialized indexed not_word actual_type =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, location, cell, initial, lookup, read, initialValue, rfl⟩ :=
        bare_resolved rfl leadingTarget
      have initialized : initial ≠ none := prefix_initialized
      cases initial with
      | none => exact absurd rfl initialized
      | some _ => exact .indexType lookup read initialValue indexed not_word actual_type
  | elementOutOfBounds projections_eq leadingTarget prefix_selected indexed arrayRead stored out_of_bounds =>
      obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projections_eq)
      obtain ⟨rfl, rfl, location, cell, initial, lookup, read, initialValue, rfl⟩ :=
        bare_resolved rfl leadingTarget
      have selected_eq : initial = _ := prefix_selected
      subst selected_eq
      exact .outOfBounds lookup read initialValue indexed arrayRead stored out_of_bounds

/-- One element has no leading key, so its keys do not fault: `keysFault` is out at one element. -/
theorem single_keys_absurd {program : Program} {registry : Registry} {size : Nat} {scope : Scope}
    {context : SourceSemantics.Context} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {place : PlaceResolution} {key : ExpressionId} {failure : Failure}
    (single : place.projections = [.element key])
    (keys : Size.Expressions program registry size scope context environment before
      (ProjectedTarget.keys place.projections) (.fault failure) after) : False := by
  simp only [single, ProjectedTarget.keys] at keys
  cases keys

end Solcore.SourceSemantics.CoreLowering.ElementAssignmentSourceInversion
end

section
/-! In-place `~` at an element place runs `bitNotElement` and its faults, or faults at the root or a
leading key by the projected rules, as an assignment does. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ElementBitNotSourceInversion
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
  | targetFault {targetSize failure after}
      (failed : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.fault failure) after) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [targetSize]) context (.fault failure) after
  | operandFault {targetSize target value after}
      (resolved : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.resolved target) after)
      (selected : target.selected = some value)
      (invalid : Dynamic.UnaryPrimitiveOperandInvalid .bitNot value) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [targetSize]) context (.fault (.semantic (.invalidUnaryOperand .bitNot))) after
  | success {targetSize tailSize target targetHeap updated written finalContext outcome after}
      (resolved : Size.ElementTarget program registry targetSize invocation context environment before
        assignment.target (.resolved target) targetHeap)
      (write : Dynamic.ResolvedPlaceWrites
        (fun _ replacement => Dynamic.BitNotAssignmentApplies assignment.target.type target.selected replacement)
        targetHeap target updated written)
      (next : Size.StatementsIn program registry mode tailSize invocation context environment written rest
        finalContext outcome after) :
      Result program registry mode invocation context environment before assignment rest
        (Size.stepSize [targetSize, tailSize]) finalContext outcome after

theorem child_and_tail {program : Program} {registry : Registry} {mode : Bool} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {assignment : AssignmentResolution}
    {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment)
    (element : ElementPlace assignment.target.projections)
    (trace : Size.StatementsIn program registry mode size invocation context environment before
      (id :: rest) finalContext outcome after) :
    Result program registry mode invocation context environment before assignment rest size finalContext outcome
      after := by
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
  | assignBareOperands actual same _ _ _ _ _ _ _ | assignBarePanic actual same _ _ _ _ _ _ _
  | assignBareUnbound actual same _ _ | assignBareDangling actual same _ _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _ | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _ | assignProjectedRhsFault actual same _ _ _ _
  | assignElement actual same _ _ _ _ _
  | assignElementTargetFault actual same _ _
  | assignElementRhsFault actual same _ _ _
  | assignElementWriteFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | letFault actual same _ _ =>
      cases (shape actual).symm.trans same
  | bitNotBare actual same snapshot _ _ =>
      cases (shape actual).symm.trans same
      have empty : assignment.target.projections = [] := by cases snapshot; assumption
      exact (element.ne_nil empty).elim
  | bitNotBareFault actual same empty _ =>
      cases (shape actual).symm.trans same
      exact (element.ne_nil empty).elim
  | bitNotProjected actual same _ _ snapshot _ _
  | bitNotProjectedOperandFault actual same _ _ snapshot _ _ =>
      cases (shape actual).symm.trans same
      exact (ElementAssignmentSourceInversion.snapshot_absurd element snapshot).elim
  | bitNotProjectedGetterFault actual same _ _ failed =>
      cases (shape actual).symm.trans same
      exact (ElementAssignmentSourceInversion.getterFault_absurd element failed).elim
  | bitNotProjectedRootFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .rootFault failed
  | bitNotProjectedKeysFault actual same _ ready keys =>
      cases (shape actual).symm.trans same
      exact .keysFault ready keys
  | bitNotElement actual same _ resolved write next =>
      cases (shape actual).symm.trans same
      exact .success resolved write next
  | bitNotElementTargetFault actual same _ failed =>
      cases (shape actual).symm.trans same
      exact .targetFault failed
  | bitNotElementOperandFault actual same _ resolved selected invalid =>
      cases (shape actual).symm.trans same
      exact .operandFault resolved selected invalid

end Solcore.SourceSemantics.CoreLowering.ElementBitNotSourceInversion
end
