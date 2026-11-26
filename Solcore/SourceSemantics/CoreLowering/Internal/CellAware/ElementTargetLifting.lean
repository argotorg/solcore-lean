import Solcore.SourceSemantics.Staging.RecursiveProfile
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize

/-!
# Element targets of one element, from the Source

The Source's resolution of a place `root[key]` of one element, plain or sized, is the staged
`ElementTarget` that resolves it to the same place and heap, and a sized Source fault of such a place
is the staged `ElementTarget` fault with the same reason and heap, given the key's liftings. The
leading place of the element is the bare root, so it resolves by `elementRoot` and faults by
`elementRootFault`; the Source rules that evaluate a path of mapping keys do not apply to an element.

Main declarations:
- `CellAwareElementTargetLifting.resolved` and `CellAwareElementTargetLifting.resolved_sized`, a
  resolution of one element;
- `CellAwareElementTargetLifting.fault_sized`, a fault of one element;
- `CellAwareElementTargetLifting.element_place` and `CellAwareElementTargetLifting.selected_ne_none`,
  the element place of the staged rules and the present snapshot of a resolution.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.CellAwareElementTargetLifting
open Frontend SourceInference

variable {program : Program} {registry : Staging.Recursive.Registry} {scope : Staging.Recursive.Scope}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {environment : Dynamic.Environment} {place : PlaceResolution} {key : ExpressionId}

/-- One element is the last projection with nothing leading it. -/
private theorem single_split {index : ExpressionId} {leading : List PlaceProjection}
    (equal : [PlaceProjection.element key] = leading ++ [.element index]) : leading = [] ∧ index = key := by
  cases leading with
  | nil =>
    simp at equal
    exact ⟨rfl, equal.symm⟩
  | cons head tail => simp at equal

/-- A bare place resolves at its root without changing the heap: the staged `elementRoot`. -/
private theorem bare_resolved {place : PlaceResolution} (bare : place.projections = []) {before after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace}
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place target after) :
    after = before ∧
      Staging.Recursive.ElementTarget program registry scope context environment before place (.resolved target)
        before := by
  obtain ⟨rfl, snapshot⟩ := Staging.Recursive.BareTarget.of_resolves bare resolve
  cases snapshot with
  | intro _ lookup read initialValue => exact ⟨rfl, .elementRoot bare lookup read initialValue⟩

/-- A sized Source fault of a bare place is its root's, at the same heap. -/
private theorem bare_fault {size : Nat} {place : PlaceResolution} (bare : place.projections = [])
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.SourcePlaceFaults program size context evidence source environment before place
      reason after) :
    after = before ∧ Staging.Recursive.ProjectedTarget.RootFault environment before place reason := by
  cases failed with
  | unbound missing => exact ⟨rfl, .unbound missing⟩
  | dangling lookup missing => exact ⟨rfl, .dangling lookup missing⟩
  | projectionExpression _ _ failed =>
    rw [bare] at failed
    cases failed
  | danglingAfterProjections lookup _ evaluate missing =>
    rw [bare] at evaluate
    cases evaluate
    exact ⟨rfl, .dangling lookup missing⟩
  | projectionRead _ _ evaluate _ _ failed =>
    rw [bare] at evaluate
    cases evaluate
    cases failed
  | uninitialized _ _ evaluate _ _ _ projected =>
    rw [bare] at evaluate
    cases evaluate
    exact absurd rfl projected
  | elementPrefix projectionsEq | elementIndex projectionsEq | elementIndexType projectionsEq
  | elementOutOfBounds projectionsEq | elementUninitialized projectionsEq =>
    rw [bare] at projectionsEq
    simp at projectionsEq

/-- A place of one element is an element place, as the staged element writes take it. -/
theorem element_place (single : place.projections = [.element key]) :
    Staging.Recursive.ElementPlace place.projections :=
  ⟨[], key, single⟩

/-- A Source resolution of a place of one element selects the element: its snapshot is present. -/
theorem selected_ne_none (single : place.projections = [.element key]) {before after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace}
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place target after) :
    target.selected ≠ none := by
  cases resolve with
  | intro _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | element => exact fun same => by cases same

/-- The Source's resolution of a place `root[key]` of one element is the staged `ElementTarget` that
resolves it, with the same place and heap, given the lifting of the key's value executions: the bare
root, then the key's word, then the array's own cell. -/
theorem resolved (single : place.projections = [.element key])
    (keyLift : ∀ {middle : Dynamic.Heap} {value : Dynamic.Value} {after : Dynamic.Heap},
      Dynamic.ExpressionEvaluates program context evidence source environment middle key value after →
      Staging.Recursive.Expression program registry scope context environment middle key (.value value) after)
    {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place target after) :
    Staging.Recursive.ElementTarget program registry scope context environment before place (.resolved target)
      after := by
  cases resolve with
  | intro _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | element projectionsEq prefixResolves prefixSelected indexed read initialValue selection =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projectionsEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves
    exact .elementStep projectionsEq leading prefixSelected (keyLift indexed) read initialValue selection

/-- The sized Source resolution of a place `root[key]` of one element is the staged `ElementTarget`
that resolves it, with the same place and heap, given the lifting of the key's value executions below
the size. -/
theorem resolved_sized {size : Nat} (single : place.projections = [.element key])
    (keyLift : ∀ {child : Nat} {middle : Dynamic.Heap} {value : Dynamic.Value} {after : Dynamic.Heap},
      child < size →
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment middle key value
        after →
      Staging.Recursive.Expression program registry scope context environment middle key (.value value) after)
    {before after : Dynamic.Heap} {target : Dynamic.ResolvedPlace}
    (resolve : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place
      target after) :
    Staging.Recursive.ElementTarget program registry scope context environment before place (.resolved target)
      after := by
  cases resolve with
  | intro _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | element projectionsEq prefixResolves prefixSelected indexed read initialValue selection =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans projectionsEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves.sound
    exact .elementStep projectionsEq leading prefixSelected
      (keyLift (SourceExecutionSize.child_lt_stepSize (by simp)) indexed) read initialValue selection

/-- A sized Source fault of a place `root[key]` of one element is the staged `ElementTarget` fault
with the same reason and heap, given the liftings of the key's value and fault executions below the
size: the root's, through the bare leading place, a root not yet initialized, the key's, a key that
is not a word, and `0x32` from the array's length on. The Source rules that evaluate a path of
mapping keys do not apply to an element. -/
theorem fault_sized {size : Nat} {reason : Dynamic.SemanticFault} (single : place.projections = [.element key])
    (keyLift : ∀ {child : Nat} {middle : Dynamic.Heap} {value : Dynamic.Value} {after : Dynamic.Heap},
      child < size →
      SourceExecutionSize.ExpressionEvaluates program child context evidence source environment middle key value
        after →
      Staging.Recursive.Expression program registry scope context environment middle key (.value value) after)
    (keyFaultLift : ∀ {child : Nat} {middle after : Dynamic.Heap}, child < size →
      SourceExecutionSize.ExpressionFaults program child context evidence source environment middle key reason
        after →
      Staging.Recursive.Expression program registry scope context environment middle key
        (.fault (.semantic reason)) after)
    {before after : Dynamic.Heap}
    (failed : SourceExecutionSize.SourcePlaceFaults program size context evidence source environment before place
      reason after) :
    Staging.Recursive.ElementTarget program registry scope context environment before place
      (.fault (.semantic reason)) after := by
  have projectionsEq : place.projections = [] ++ [.element key] := single
  cases failed with
  | unbound missing => exact .elementPrefixFault projectionsEq (.elementRootFault rfl (.unbound missing))
  | dangling lookup missing =>
    exact .elementPrefixFault projectionsEq (.elementRootFault rfl (.dangling lookup missing))
  | projectionExpression _ _ failed =>
    rw [single] at failed
    cases failed
  | danglingAfterProjections _ _ evaluate | projectionRead _ _ evaluate | uninitialized _ _ evaluate =>
    rw [single] at evaluate
    cases evaluate
  | elementPrefix leadingEq failed =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans leadingEq)
    obtain ⟨rfl, root⟩ := bare_fault rfl failed
    exact .elementPrefixFault leadingEq (.elementRootFault rfl root)
  | elementIndex leadingEq prefixResolves initialized failed =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans leadingEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves.sound
    exact .elementIndexFault leadingEq leading initialized
      (keyFaultLift (SourceExecutionSize.child_lt_stepSize (by simp)) failed)
  | elementIndexType leadingEq prefixResolves initialized indexed notWord actualType =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans leadingEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves.sound
    exact .elementIndexType leadingEq leading initialized
      (keyLift (SourceExecutionSize.child_lt_stepSize (by simp)) indexed) notWord actualType
  | elementOutOfBounds leadingEq prefixResolves prefixSelected indexed read stored outOfBounds =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans leadingEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves.sound
    exact .elementOutOfBounds leadingEq leading prefixSelected
      (keyLift (SourceExecutionSize.child_lt_stepSize (by simp)) indexed) read stored outOfBounds
  | elementUninitialized leadingEq prefixResolves prefixEmpty =>
    obtain ⟨rfl, rfl⟩ := single_split (single.symm.trans leadingEq)
    obtain ⟨rfl, leading⟩ := bare_resolved (registry := registry) (scope := scope) rfl prefixResolves.sound
    exact .elementUninitialized leadingEq leading prefixEmpty

end Solcore.SourceSemantics.CoreLowering.CellAwareElementTargetLifting
