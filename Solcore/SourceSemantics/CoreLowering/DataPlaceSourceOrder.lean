import Solcore.SourceSemantics.Dynamic.Initialization

/-! Source ordering facts used when reflecting the Core modifier before the
latest-root setter. An absent snapshot has no projections, and a successfully
resolved nonempty ordinary root cannot become uninitialized during the RHS. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

theorem read_none {initial : Option Value} {projections : List EvaluatedProjection}
    (read : ProjectionsRead initial projections none) : initial = none ∧ projections = [] := by
  have aux : ∀ {current : Option Value} {path : List EvaluatedProjection} {selected : Option Value},
      ProjectionsRead current path selected → selected = none → current = none ∧ path = [] := by
    intro current path selected selectedBy
    induction selectedBy with
    | nil => intro absent; exact ⟨absent, rfl⟩
    | indexFound _ _ ih => intro absent; cases (ih absent).1
    | indexDefault _ _ _ ih => intro absent; cases (ih absent).1
    | member _ _ ih => intro absent; cases (ih absent).1
  exact aux read rfl

theorem resolve_none {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (resolve : SourcePlaceResolves program context evidence source environment before place target after)
    (absent : target.selected = none) : target.projections = [] := by
  cases resolve with
  | intro lookup initialRead keys currentRead root selection =>
    simp only at absent
    rw [absent] at selection
    exact (read_none selection).2

/-- The resolved target retains the declaration type of the original root.
Index expression effects may change its value, but preserve this metadata. -/
theorem resolve_root_type {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace}
    (resolve : SourcePlaceResolves program context evidence source environment before place target after)
    (metadata : HeapMetadataExtend before after) {location : Location} {cell : Cell}
    (lookup : Environment.LooksUp environment place.root location)
    (read : Heap.Reads before location cell) : target.rootType = cell.type := by
  cases resolve with
  | intro actualLookup initialRead keys currentRead root selection =>
    have same := lookup.functional actualLookup
    subst_vars
    obtain ⟨current, selected, sameType, _⟩ := metadata _ _ read
    have same := currentRead.functional selected
    subst_vars
    exact sameType

/-- Latest-root absence contradicts a successfully resolved nonempty path.
Virtual empty mappings are handled separately by their retained source type;
the initialized-location invariant is derived from the actual RHS trace. -/
theorem latest_uninitialized_impossible {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment} {before targetHeap after : Heap}
    {place : PlaceResolution} {target : ResolvedPlace} {id : ExpressionId} {right : Value}
    (resolve : SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (rhs : ExpressionEvaluates program context evidence source environment targetHeap id right after)
    {current : Cell} (read : Heap.Reads after target.location current)
    (sameType : current.type = target.rootType) (absent : RootInitialValue current none)
    (nonempty : target.projections ≠ []) : False := by
  cases resolve with
  | intro lookup initialRead keys oldRead oldRoot selection =>
    cases absent with
    | uninitialized notMapping =>
      cases oldRoot with
      | initialized =>
        obtain ⟨latest, latestRead, present⟩ := rhs.initialization_extends _ _ oldRead (by simp)
        have same := read.functional latestRead
        subst latest
        exact present rfl
      | emptyMapping key value => exact notMapping ⟨key, value, sameType⟩
      | uninitialized => cases selection; exact nonempty rfl

end Solcore.SourceSemantics.CoreLowering.DataPlaceSourceOrder
