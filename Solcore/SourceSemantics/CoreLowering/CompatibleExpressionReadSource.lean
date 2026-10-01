import Solcore.SourceSemantics.Dynamic.Fault

/-! Local uniqueness of independent ordinary source reads, including lazy
mapping initialization. This uses their actual source derivations and readable
ordinary cell, and makes no whole-language determinism assumption. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
open Frontend SourceInference

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem cellsWrite_unique {cells left right : List Dynamic.Cell} {index : Nat} {value : Dynamic.Cell}
    (first : Dynamic.Heap.CellsWrite cells index value left)
    (second : Dynamic.Heap.CellsWrite cells index value right) : left = right := by
  induction first generalizing right with
  | head => cases second; rfl
  | tail _ ih => cases second with | tail second => exact congrArg (_ :: ·) (ih second)

private theorem writes_unique {before left right : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (first : Dynamic.Heap.Writes before location value left)
    (second : Dynamic.Heap.Writes before location value right) : left = right := by
  cases first with
  | intro firstRead firstWrite =>
    cases second with
    | intro secondRead secondWrite =>
      have same := firstRead.functional secondRead
      cases same
      cases cellsWrite_unique firstWrite secondWrite
      rfl

private inductive ReadResult (heap : Dynamic.Heap) (location : Dynamic.Location) (cell : Dynamic.Cell) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | initialized {value} (stored : cell.value = some value) : ReadResult heap location cell (.value value) heap
  | mapping {key value after} (type : cell.type = .mapping key value) (empty : cell.value = none)
      (written : Dynamic.Heap.Writes heap location (some (.mapping key value [])) after) :
      ReadResult heap location cell (.value (.mapping key value [])) after
  | uninitialized (empty : cell.value = none) (notMapping : ¬ ∃ key value, cell.type = .mapping key value) :
      ReadResult heap location cell (.fault (.uninitializedLocation location)) heap

private theorem ReadResult.unique {heap firstHeap secondHeap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    {first second : Dynamic.ExpressionOutcome} (left : ReadResult heap location cell first firstHeap)
    (right : ReadResult heap location cell second secondHeap) : first = second ∧ firstHeap = secondHeap := by
  cases left with
  | initialized stored =>
    cases right with
    | initialized other => cases Option.some.inj (stored.symm.trans other); exact ⟨rfl, rfl⟩
    | mapping _ empty _ | uninitialized empty _ => rw [stored] at empty; cases empty
  | mapping type empty written =>
    cases right with
    | initialized stored => rw [empty] at stored; cases stored
    | mapping other _ secondWrite =>
      obtain ⟨rfl, rfl⟩ := TypeSystem.Ty.mapping.inj (type.symm.trans other)
      exact ⟨rfl, writes_unique written secondWrite⟩
    | uninitialized _ notMapping => exact False.elim (notMapping ⟨_, _, type⟩)
  | uninitialized empty notMapping =>
    cases right with
    | initialized stored => rw [empty] at stored; cases stored
    | mapping type _ _ => exact False.elim (notMapping ⟨_, _, type⟩)
    | uninitialized => exact ⟨rfl, rfl⟩

private theorem result_of_trace {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {outcome : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location) (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id outcome after) :
    ReadResult heap location cell outcome after := by
  have align : ∀ {otherLocation otherCell},
      Dynamic.Environment.LooksUp environment binder otherLocation → Dynamic.Heap.Reads heap otherLocation otherCell →
      otherLocation = location ∧ otherCell = cell := by
    intro otherLocation otherCell otherLookup otherRead
    have sameLocation := otherLookup.functional lookup
    subst otherLocation
    exact ⟨rfl, otherRead.functional read⟩
  cases trace with
  | value evaluated =>
    cases evaluated with
    | intro otherContains raw path =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [coercions] at path
      cases path
      rw [form] at raw
      cases raw with
      | «local» _ otherLookup otherRead _ initialized =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .initialized initialized
      | localEmptyMapping _ otherLookup otherRead _ type empty written =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .mapping type empty written
    | generalizedLocal otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at otherForm
      cases otherForm
      obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor
  | fault failed =>
    cases failed with
    | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
    | form otherContains raw =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at raw
      cases raw with
      | localUnbound _ unbound => exact False.elim (unbound.excludes_lookup lookup)
      | localDangling _ otherLookup dangling =>
        have same := otherLookup.functional lookup
        subst_vars
        exact False.elim (dangling.excludes_read read)
      | localUninitialized _ otherLookup otherRead _ empty notMapping =>
        obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
        exact .uninitialized empty notMapping
    | coercion otherContains _ failed =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [coercions] at failed
      cases failed
    | generalizedLocalRequirement otherContains otherForm _ otherLookup otherRead descriptor _ _ _
    | generalizedLocalCoercion otherContains otherForm _ otherLookup otherRead descriptor _ _ _ =>
      have same := contains_unique unique otherContains contains
      subst_vars
      rw [form] at otherForm
      cases otherForm
      obtain ⟨rfl, rfl⟩ := align otherLookup otherRead
      rw [ordinary] at descriptor
      cases descriptor

/-- This uniqueness statement is restricted to a readable ordinary local.
Generalized closure instantiation and arbitrary source calls are not included. -/
theorem source_outcome_unique {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap firstHeap secondHeap : Dynamic.Heap}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {location : Dynamic.Location} {cell : Dynamic.Cell} {first second : Dynamic.ExpressionOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (lookup : Dynamic.Environment.LooksUp environment binder location) (read : Dynamic.Heap.Reads heap location cell)
    (ordinary : cell.generalized = none)
    (left : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id first firstHeap)
    (right : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment heap id second secondHeap) :
    first = second ∧ firstHeap = secondHeap :=
  (result_of_trace unique contains form coercions lookup read ordinary left).unique
    (result_of_trace unique contains form coercions lookup read ordinary right)

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReads
