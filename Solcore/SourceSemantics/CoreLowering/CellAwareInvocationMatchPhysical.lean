import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationPhysicalExtension
import Solcore.SourceSemantics.CoreLowering.DataMatchBranchPrefix

/-! Match prefixes retain the actual invocation's frame and generalized local
entries. The hidden native slot has no Source declaration; successful pattern
bindings are the ordinary cells allocated by the independent Source trace. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
open Core Frontend SourceInference TypeSystem GeneralHeap
open CellAwareInvocationPhysical

private theorem full_internal {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context : SourceSemantics.Context} {internal : Resolved.LocalId} (payload : Core.Ty)
    (absent : internal ∉ (SourceCoreDataPlaces.declaredBinders source).map (·.id))
    (declarations : CellAwareScopeDeclarations.Full source scope context) :
    CellAwareScopeDeclarations.Full source ((internal, payload) :: scope) context := by
  intro id declared index type selected authentic
  by_cases same : internal = id
  · subst id
    have present : declared ∈ (SourceCoreDataPlaces.declaredBinders source).filter
        (fun candidate => decide (candidate.id = internal)) := by
      rw [authentic]
      exact List.mem_singleton_self declared
    obtain ⟨member, sameId⟩ := List.mem_filter.mp present
    exact False.elim (absent (List.mem_map.mpr ⟨declared, member, of_decide_eq_true sameId⟩))
  · simp only [SourceCoreLocalCell.lookup?, same, ↓reduceIte] at selected
    cases previous : SourceCoreLocalCell.lookup? scope id with
    | none => simp [previous] at selected
    | some entry => exact declarations _ _ _ _ previous authentic

private theorem full_binders {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {context final : SourceSemantics.Context} {bindings : List (TypedBinder × Core.Ty)}
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders source)
    (extended : BindersExtend source.owner context (bindings.map Prod.fst) final)
    (declarations : CellAwareScopeDeclarations.Full source scope context) :
    CellAwareScopeDeclarations.Full source
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) scope) final := by
  induction bindings generalizing context scope with
  | nil => cases extended; exact declarations
  | cons binding rest ih =>
    cases extended with
    | cons head tail =>
      exact ih (fun binder present => members binder (List.mem_cons_of_mem _ present)) tail
        (CellAwareScopeDeclarations.scope_bind binding.2 (members binding.1 List.mem_cons_self) declarations head)

private theorem binders_preserve_read {environment finalEnvironment : Dynamic.Environment}
    {heap finalHeap : Dynamic.Heap} {binders : List TypedBinder} {values : List Dynamic.Value}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    {location cell} (read : Dynamic.Heap.Reads heap location cell) :
    Dynamic.Heap.Reads finalHeap location cell := by
  induction allocated with
  | nil => exact read
  | cons allocation _ ih => exact ih (allocation.preserves_read read)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {attachment : optParam
    (Dynamic.GeneralizedClosure → SourceCoreLocalPolymorphism.Binding → TypeSystem.Substitution → Prop)
    (fun _ _ _ => True)}
  {bodyRelation : ActualBodyInvocation.BodyRelation}
  {index : ActualBodyInvocation.Index compiled bodyRelation}

private theorem allocated_entries {context finalContext : SourceSemantics.Context}
    {frameLocation mapping world store environment finalEnvironment heap finalHeap binders values}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    (extended : BindersExtend index.source.owner context binders finalContext)
    (entries : ∀ {id location}, Dynamic.Environment.LooksUp environment id location →
      Entry (attachment := attachment) compiled index context frameLocation id location mapping world finalHeap store) :
    ∀ {id location}, Dynamic.Environment.LooksUp finalEnvironment id location →
      Entry (attachment := attachment) compiled index finalContext frameLocation id location mapping world finalHeap store := by
  induction allocated generalizing context finalContext with
  | nil => cases extended; exact entries
  | cons allocation tail ih =>
    cases extended with
    | cons head remaining =>
      apply ih remaining
      intro id location lookup
      cases lookup with
      | head => exact .ordinary (binders_preserve_read tail allocation.reads_new) rfl
      | tail different previous => exact (entries previous).recontext head different

theorem allocated_authority {mapping world store environment finalEnvironment heap finalHeap binders values}
    (allocated : Dynamic.BindersAllocate environment heap binders values finalEnvironment finalHeap)
    (authority : CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world finalHeap store environment) :
    CellAwareScopeAuthority.At (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      index.owner index.active mapping world finalHeap store finalEnvironment := by
  induction allocated with
  | nil => exact authority
  | cons allocation tail ih =>
    exact ih (.cons (.ordinary (binders_preserve_read tail allocation.reads_new) rfl) authority)

/-- The actual selected arm uses the same invocation, caller and active
substitution. Its new cells come from BindersAllocate; old descriptor rows
come from the concrete match-prefix effect. -/
def arm {context finalContext : SourceSemantics.Context}
    {scope canonical mapping world heap store environment hiddenHeap finalHeap finalEnvironment
      finalCanonical finalMap finalWorld finalStore internal payload}
    {bindings : List (TypedBinder × Core.Ty)} {values : List Dynamic.Value}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (hidden : internal ∉ (SourceCoreDataPlaces.declaredBinders index.source).map (·.id))
    (members : ∀ binder ∈ bindings.map Prod.fst, binder ∈ SourceCoreDataPlaces.declaredBinders index.source)
    (extended : BindersExtend index.source.owner context (bindings.map Prod.fst) finalContext)
    (allocated : Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) values finalEnvironment finalHeap)
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store finalMap finalWorld finalHeap finalStore)
    (reference : finalCanonical[(bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current)
        ((internal, payload) :: scope)).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type physical.location))
    (read : finalStore.read? physical.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame physical.native))
    (unmapped : physical.location ∉ finalMap) :
    Physical (attachment := attachment) compiled index finalContext
      (bindings.foldl (fun current binding => (binding.1.id, binding.2) :: current) ((internal, payload) :: scope))
      finalCanonical finalMap finalWorld finalHeap finalStore finalEnvironment :=
  ⟨physical.frame,
    CompatibleMatchArmScopes.scope_binders
      (CompatibleMatchArmScopes.scope_internal payload hidden physical.declarations) members extended,
    physical.ownership, full_binders members extended (full_internal payload hidden physical.sourceDeclarations),
    physical.location, reference, read, unmapped,
    allocated_entries allocated extended (fun lookup => (physical.entries lookup).transport effect)⟩

/-- A default or empty selection exposes only the internal scrutinee slot. -/
def parent {context : SourceSemantics.Context}
    {scope canonical mapping world heap store environment finalHeap finalCanonical finalMap finalWorld finalStore internal payload}
    (physical : Physical (attachment := attachment) compiled index context scope canonical mapping world heap store environment)
    (hidden : internal ∉ (SourceCoreDataPlaces.declaredBinders index.source).map (·.id))
    (effect : CellAwareScopeAuthority.Effect (GeneralizedLocalAcceptedInstances.modelWith compiled.indexed attachment)
      mapping world heap store finalMap finalWorld finalHeap finalStore)
    (reference : finalCanonical[((internal, payload) :: scope).length + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type physical.location))
    (read : finalStore.read? physical.location =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame physical.native))
    (unmapped : physical.location ∉ finalMap) :
    Physical (attachment := attachment) compiled index context ((internal, payload) :: scope)
      finalCanonical finalMap finalWorld finalHeap finalStore environment :=
  ⟨physical.frame, CompatibleMatchArmScopes.scope_internal payload hidden physical.declarations,
    physical.ownership, full_internal payload hidden physical.sourceDeclarations,
    physical.location, reference, read, unmapped, fun lookup => (physical.entries lookup).transport effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationMatchPhysical
