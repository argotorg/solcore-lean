import Solcore.SourceSemantics.CoreLowering.ScalarExpressionReflection
import Solcore.SourceSemantics.CoreLowering.GeneralHeapFrame

/-! Inversion of an independently supplied bare-local equal assignment. The
scalar RHS cannot mutate the heap, so the captured root and latest root still
refer to the represented cell; source and Core locations may differ. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection

open Frontend Frontend.SourceInference TypeSystem LocalCell

theorem resolve_bare
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {heap after : Dynamic.Heap}
    {place : PlaceResolution} {target : Dynamic.ResolvedPlace}
    (bare : place.projections = [])
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment heap place target after) :
    after = heap ∧ target.projections = [] ∧
      Dynamic.Environment.LooksUp environment place.root target.location := by
  cases resolved with
  | intro lookup _ projections _ _ _ =>
      rw [bare] at projections
      cases projections
      exact ⟨rfl, rfl, lookup⟩

theorem source_success
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {rhs : ExpressionId} {payload : Core.Ty} {code : Core.Expr} {depth index : Nat}
    {place : PlaceResolution} {updatedRoot : Dynamic.Value}
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (unique : NodeOccurrencesUnique source)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, payload)) (bare : place.projections = [])
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies .equal)
      environment heap place rhs updatedRoot after) :
    ∃ staged : SourceStagedValue.Value, ∃ target finalStore,
      updatedRoot = StagedValue.toSource staged ∧ SourceStagedValue.coreType staged = payload ∧
      Core.Evaluates coreEnvironment store code (.inRight .word (SourceStagedValue.toCore staged)) store ∧
      coreEnvironment[index]? = some (.cellRef (Core.OptionalCell.cellType payload) target) ∧
      (∃ previous, store.read? target = some previous) ∧
      store.write? target (.inRight .unit (SourceStagedValue.toCore staged)) = some finalStore ∧
      GeneralHeap.HeapRepresents mapping world after finalStore ∧
      GeneralHeap.AdministrativePreserved mapping store mapping finalStore := by
  cases execution with
  | intro resolve rhsEvaluation written =>
      obtain ⟨rfl, projections, targetLookup⟩ := resolve_bare bare resolve
      obtain ⟨rfl, staged, rfl, typed, core⟩ := ScalarExpressionReflection.Primitive.source_success value unique environments heaps rhsEvaluation
      obtain ⟨sourceLocation, target, cell, stored, lookup, coreLookup, reference, _, coreRead, _⟩ :=
        environments.lookup_heap heaps slot
      have sameLocation := Dynamic.Environment.LooksUp.functional targetLookup lookup
      cases written with
      | intro _ _ _ update write =>
          rw [projections] at update
          cases update with
          | leaf applied =>
              cases applied
              rw [sameLocation] at write
              obtain ⟨finalStore, coreWrite, finalHeaps⟩ := heaps.write_initialized reference staged typed write
              exact ⟨staged, target, finalStore, rfl, typed, core, coreLookup, ⟨stored, coreRead⟩,
                coreWrite, finalHeaps, GeneralHeap.AdministrativePreserved.write (List.mem_of_getElem? reference.mapped) coreWrite⟩

theorem target_cannot_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {index : Nat} {payload : Core.Ty}
    {place : PlaceResolution} {reason : Dynamic.SemanticFault}
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, payload)) (bare : place.projections = [])
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (fault : Dynamic.SourcePlaceFaults program context evidence source environment heap place reason after) : False := by
  obtain ⟨location, _, _, _, lookup, _, _, read, _, _⟩ := environments.lookup_heap heaps slot
  cases fault with
  | unbound missing => exact missing.excludes_lookup lookup
  | dangling otherLookup missing =>
      have same := Dynamic.Environment.LooksUp.functional lookup otherLookup
      subst_vars
      exact missing.excludes_read read
  | projectionExpression _ _ fault => rw [bare] at fault; cases fault
  | danglingAfterProjections otherLookup _ projections missing =>
      rw [bare] at projections
      cases projections
      have same := Dynamic.Environment.LooksUp.functional lookup otherLookup
      subst_vars
      exact missing.excludes_read read
  | projectionRead _ _ projections _ _ fault =>
      rw [bare] at projections
      cases projections
      cases fault
  | uninitialized _ _ projections _ _ _ nonempty =>
      rw [bare] at projections
      cases projections
      exact nonempty rfl

private theorem equal_operands_valid {previous : Option Dynamic.Value} {right : Dynamic.Value}
    (invalid : Dynamic.AssignmentOperandsInvalid .equal previous right) : False := by
  cases invalid with
  | uninitialized notEqual => exact notEqual rfl
  | compound corresponds _ => cases corresponds

/-- Plain assignment ignores its old leaf, including an uninitialized leaf.
Its only modeled fault under this profile is the RHS's exact read fault. -/
theorem source_fault
    {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {reasonAt : ExpressionId → Core.Word} {rhs : ExpressionId} {payload : Core.Ty} {code : Core.Expr} {depth index : Nat}
    {place : PlaceResolution} {reason : Dynamic.SemanticFault}
    (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payload code depth)
    (unique : NodeOccurrencesUnique source)
    (valid : PrimitiveExpressions.ContextValid compilation context) (covers : evidence.Covers context)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, payload)) (bare : place.projections = [])
    {mapping : GeneralHeap.LocationMap} {world : Core.StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Core.Environment}
    {heap after : Dynamic.Heap} {store : Core.Store}
    (environments : GeneralHeap.EnvRepresents mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GeneralHeap.HeapRepresents mapping world heap store)
    (execution : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment heap place .equal rhs reason after) :
    after = heap ∧ ∃ site location,
      reason = .uninitializedLocation location ∧
      PrimitiveExpressions.UninitializedAt program context evidence source environment heap rhs site location ∧
      Core.Evaluates coreEnvironment store code (.inLeft payload (.word (reasonAt site))) store := by
  cases execution with
  | target fault => exact False.elim (target_cannot_fault slot bare environments heaps fault)
  | rhs resolve fault =>
      obtain ⟨rfl, _, _⟩ := resolve_bare bare resolve
      exact ScalarExpressionReflection.Primitive.source_fault value unique valid covers environments heaps fault
  | operands _ _ _ _ _ _ invalid => exact False.elim (equal_operands_valid invalid)
  | structuralUpdate resolve _ _ _ _ fault =>
      obtain ⟨_, projections, _⟩ := resolve_bare bare resolve
      rw [projections] at fault
      cases fault

end Solcore.SourceSemantics.CoreLowering.ScalarAssignmentReflection
