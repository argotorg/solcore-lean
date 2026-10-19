import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogNativeContexts
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchArmScopes

/-! The initial named body scope retains the original source parameter schemes.
A successful declaration lookup is authenticated against the actual inputs;
no success is invented for duplicate or qualified declarations. Native payload
types do not determine source types, and no runtime authority is inferred. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
open Core Frontend SourceInference
open CallableAncestryPairedLookup RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts

/-- Exact declaration correspondence also retains polymorphic source schemes. -/
def Full (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (context : SourceSemantics.Context) : Prop :=
  ∀ binder declared index type,
    SourceCoreLocalCell.lookup? scope binder = some (index, type) →
    (SourceCoreDataPlaces.declaredBinders source).filter (fun actual => decide (actual.id = binder)) = [declared] →
    Resolved.LocalScope.Lookup context.locals binder declared.scheme

private theorem identifies {source : TypedSource} {binder declared : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (authentic : (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) = [declared]) : declared = binder := by
  have present : binder ∈ (SourceCoreDataPlaces.declaredBinders source).filter
      (fun actual => decide (actual.id = binder.id)) := List.mem_filter.mpr ⟨member, by simp⟩
  rw [authentic] at present
  exact (List.mem_singleton.mp present).symm

/-- Installing a real source binder keeps lookup correspondence even if an
unrelated declared binder would make a future compiler lookup fail. -/
theorem scope_bind {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context next : SourceSemantics.Context} {binder : TypedBinder} (payload : Core.Ty)
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (declarations : Full source scope context)
    (extended : BinderExtends source.owner context binder next) :
    Full source ((binder.id, payload) :: scope) next := by
  cases extended
  intro id declared index type selected authentic
  by_cases same : binder.id = id
  · subst id
    have identified := identifies member authentic
    subst declared
    exact .head
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact .tail same (declarations _ _ _ _ previous authentic)

/-- Source-order installation and the compiler's reversed scope agree. The
native payload vector is arbitrary; only original binder identities matter. -/
theorem parameters {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context final : SourceSemantics.Context} {bindings : List (TypedBinder × Core.Ty)} {types : List TypeSystem.Ty}
    (member : ∀ binding, binding ∈ bindings → binding.1 ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : MonoBindersExtend source.owner context (bindings.map Prod.fst) types final)
    (declarations : Full source scope context) :
    Full source
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope) final := by
  induction bindings generalizing context scope types with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    cases extended with
    | cons _ head tail =>
      exact ih (fun candidate present => member candidate (List.mem_cons_of_mem _ present)) tail
        (scope_bind binding.2 (member binding List.mem_cons_self) declarations head)

private theorem reversed_scope (bindings : List (TypedBinder × Core.Ty)) (scope : SourceCoreLocalCell.Scope) :
    bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope =
      bindings.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
  induction bindings generalizing scope with
  | nil => rfl
  | cons binding rest ih => simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, List.append_assoc, List.cons_append, List.nil_append]

/-- Every real named Header supplies its initial body's source declaration
correspondence. Residual flags, source schemes and the complete input order
are unchanged. This does not claim that every rootBinder call succeeds. -/
theorem header_scope {checked : Checked} {base : Base checked}
    {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
    {values : SourceCoreCompatibleValues.Context} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    {program : Program} (header : Header prepared values ambient.definitions program) :
    Full header.function.source (bodyScope header) header.context := by
  have members : ∀ binding, binding ∈ header.bindings →
      binding.1 ∈ SourceCoreDataPlaces.declaredBinders header.function.source := by
    intro binding member
    have input : binding.1 ∈ header.function.source.inputs := by
      rw [header.inputs]
      exact List.mem_map.mpr ⟨binding, member, rfl⟩
    exact List.mem_append_left _ input
  have extended := header.extended
  rw [header.parameters] at extended
  have initial : Full header.function.source [] header.function.context := by
    intro _ _ _ _ selected _
    cases selected
  have final := parameters members extended initial
  simpa only [reversed_scope, List.append_nil, bodyScope] using final

end Solcore.SourceSemantics.CoreLowering.CellAwareScopeDeclarations
