import Solcore.SourceSemantics.CoreLowering.DataPayloadDefaults

/-! Finite catalog-entry receipts suffice for the mapping/proxy layout laws.
Outer staging erasure is handled structurally; nominal arguments and proxy
inner identities are preserved by the actual catalog's erase operation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference

theorem erase_idempotent (type : TypeSystem.Ty) :
    SourceCoreDataCatalog.erase (SourceCoreDataCatalog.erase type) = SourceCoreDataCatalog.erase type := by
  induction type <;> simp_all [SourceCoreDataCatalog.erase]

theorem identity_erase (catalog : SourceCoreDataCatalog.Catalog) (type : TypeSystem.Ty) :
    catalog.identity? (SourceCoreDataCatalog.erase type) = catalog.identity? type := by
  simp [SourceCoreDataCatalog.Catalog.identity?, erase_idempotent]

theorem project_erase_ok (catalog : SourceCoreDataCatalog.Catalog) (type : TypeSystem.Ty) (core : Ty) :
    catalog.project (SourceCoreDataCatalog.erase type) = .ok core ↔ catalog.project type = .ok core := by
  induction type generalizing core with
  | product left right first second | function left right first second =>
    cases a : catalog.project left <;> cases ae : catalog.project (SourceCoreDataCatalog.erase left) <;>
      cases b : catalog.project right <;> cases be : catalog.project (SourceCoreDataCatalog.erase right) <;>
      simp_all [SourceCoreDataCatalog.erase, SourceCoreDataCatalog.Catalog.project, bind, Except.bind, pure, Except.pure]
    all_goals
      have aSame := (first _).mp rfl
      have bSame := (second _).mp rfl
      subst_vars; rfl
  | comptime inner ih => exact ih core
  | mapping key value =>
    have identity := identity_erase catalog (.mapping key value)
    simp only [SourceCoreDataCatalog.erase] at identity ⊢
    simp only [SourceCoreDataCatalog.Catalog.project, identity]
    cases selected : catalog.identity? (.mapping key value) <;> simp [pure, Except.pure]
  | constructor | «variable» | parameter | error | application | proxy => rfl

/-- Only entries that declare a mapping or proxy need a special layout. The
same receipt can be checked once for each finite actual catalog entry. -/
def EntryLayout (catalog : SourceCoreDataCatalog.Catalog) (id : DataTypeId)
    (entry : SourceCoreDataCatalog.Entry) : Prop :=
  match entry.sourceType with
  | .proxy _ => catalog.definitions.lookupConstructorPayloadType? ⟨id, 0⟩ = some .unit
  | .mapping key value => ∃ keyType valueType,
      catalog.project key = .ok keyType ∧ catalog.project value = .ok valueType ∧
      (Core.OrderedMapping.Layout.mk keyType valueType id).Registered catalog.definitions
  | _ => True

theorem CatalogLayouts.of_entries {catalog : SourceCoreDataCatalog.Catalog}
    (entries : ∀ id entry, catalog.entries[id.index]? = some entry → EntryLayout catalog id entry) :
    CatalogLayouts catalog := by
  constructor
  · intro inner id identity
    obtain ⟨entry, selected, sourceType⟩ := DataEqualityValues.identity_entry identity
    have layout := entries id entry selected
    simp only [SourceCoreDataCatalog.erase] at sourceType
    simpa only [EntryLayout, sourceType] using layout
  · intro key value id identity
    obtain ⟨entry, selected, sourceType⟩ := DataEqualityValues.identity_entry identity
    have layout := entries id entry selected
    simp only [SourceCoreDataCatalog.erase] at sourceType
    simp only [EntryLayout, sourceType] at layout
    obtain ⟨keyType, valueType, keyProjected, valueProjected, registered⟩ := layout
    exact ⟨keyType, valueType, (project_erase_ok catalog key keyType).mp keyProjected,
      (project_erase_ok catalog value valueType).mp valueProjected, registered⟩

end Solcore.SourceSemantics.CoreLowering.DataPayload
