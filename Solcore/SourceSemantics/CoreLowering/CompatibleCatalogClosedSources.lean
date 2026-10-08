import Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix

/-! The actual catalog registration supplies closure of its Source entries.
Successful projections then establish raw Source closure, including erased
staging wrappers. Native well-formedness and occurrence graph closure are
separate facts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
open Core Frontend SourceInference SourceCoreCompatibleCatalog CompatibleCatalogRegistrationPrefix

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Canonicalization preserves exactly the closed-type predicate. -/
theorem runtime_closed (type : TypeSystem.Ty) :
    SourceCoreDataCatalog.closed (SourceCoreRawMetadata.runtimeType type) = SourceCoreDataCatalog.closed type := by
  induction type <;> simp_all [SourceCoreDataCatalog.closed, SourceCoreRawMetadata.runtimeType]

/-- The authentic factory starts with no entries and retains Source closure
through the original registration fold and its unchanged checking suffix. -/
theorem prepare_closed {signatures : ProgramSignatures} {fuel : Nat} {types : List TypeSystem.Ty}
    {metadata : List SourceCoreRawMetadata.Metadata} {limits : SourceCoreRawMetadata.Limits}
    {profile : Bool} {checked : Checked}
    (accepted : SourceCoreCompatibleCatalog.prepare signatures fuel types metadata limits profile = .ok checked) :
    ClosedSources checked.catalog := by
  unfold SourceCoreCompatibleCatalog.prepare at accepted
  obtain ⟨registered, generated, accepted⟩ := bind_ok accepted
  obtain ⟨catalog, nativeTypes⟩ := registered
  have closed : ClosedSources catalog :=
    ((registered_prefix_with_closed signatures fuel).2 _ _ _ _ generated).closed (by
      intro entry member; cases member)
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  obtain ⟨seen, original⟩ := discovered
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; exact closed
    · cases accepted

/-- A genuine identity lookup selects a closed original registry entry. -/
theorem identity_closed {catalog : Catalog} (closed : ClosedSources catalog)
    {type : TypeSystem.Ty} {identity : DataTypeId}
    (found : catalog.identity? type = some identity) : SourceCoreDataCatalog.closed type = true := by
  unfold Catalog.identity? at found
  cases selected : catalog.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) with
  | none => simp only [selected, Option.map_none] at found; cases found
  | some item =>
    have member := List.fst_mem_of_mem_zipIdx (List.mem_of_find?_eq_some selected)
    have same := of_decide_eq_true (List.find?_some (p := fun item : Entry × Nat =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type)) selected)
    have actual := closed item.1 member
    rw [same, runtime_closed] at actual
    exact actual

/-- Static projection inversion supplies closure of the raw Source type.
This proof traverses type syntax and performs no execution. -/
theorem project_closed {catalog : Catalog} (closed : ClosedSources catalog)
    {type : TypeSystem.Ty} {native : Core.Ty}
    (accepted : catalog.project type = .ok native) : SourceCoreDataCatalog.closed type = true := by
  induction type generalizing native with
  | constructor constructor => rfl
  | product left right leftIH rightIH
  | function left right leftIH rightIH =>
    unfold Catalog.project at accepted
    obtain ⟨first, leftAccepted, remaining⟩ := bind_ok accepted
    obtain ⟨last, rightAccepted, _⟩ := bind_ok remaining
    change (SourceCoreDataCatalog.closed left && SourceCoreDataCatalog.closed right) = true
    rw [leftIH leftAccepted, rightIH rightAccepted]
    rfl
  | comptime inner ih => exact ih accepted
  | mapping key value _ _ =>
    unfold Catalog.project at accepted
    cases found : catalog.identity? (.mapping key value) with
    | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
    | some identity => exact identity_closed closed found
  | «variable» id | parameter id | error | application left right _ _ | proxy inner _ =>
    unfold Catalog.project at accepted
    split at accepted
    · exact identity_closed closed (by assumption)
    · cases accepted

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogClosedSources
