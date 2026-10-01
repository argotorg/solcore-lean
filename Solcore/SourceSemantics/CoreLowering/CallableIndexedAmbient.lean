import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.SourceSemantics.CoreLowering.AmbientDefinitions

/-! The full indexed compiler's owned preparation receipts determine the
actual base/frame/marker definition prefix. Source catalog identities remain
unchanged, and no arbitrary full environment is identified with the base.
This is a static layout certificate, not source closure authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem codebook_ambient {ambient : DataEnvironment}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory} {first : Nat}
    {prepared : SourceCoreAllocationCodebook.Prepared}
    (accepted : SourceCoreAllocationCodebook.prepare ambient inventories first = .ok prepared) :
    prepared.ambient = ambient := by
  unfold SourceCoreAllocationCodebook.prepare at accepted
  split at accepted
  · obtain ⟨_, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨_, _, accepted⟩ := bind_ok accepted
      split at accepted
      · cases accepted; rfl
      · split at accepted
        · cases accepted
        · split at accepted <;> cases accepted
    · cases accepted
  · cases accepted

theorem discovery_ambient {ambient : DataEnvironment}
    {contexts : List SourceCoreAllocationDiscovery.Context} {first : Nat}
    {prepared : SourceCoreAllocationDiscovery.Prepared}
    (accepted : SourceCoreAllocationDiscovery.prepare ambient contexts first = .ok prepared) :
    prepared.ambient = ambient := by
  unfold SourceCoreAllocationDiscovery.prepare at accepted
  have extract {α β ε : Type} (f : α → β) {input : Except ε α} {output : β}
      (accepted : input.map f = .ok output) : ∃ value, input = .ok value ∧ f value = output := by
    cases input with
    | error => cases accepted
    | ok value => exact ⟨value, rfl, Except.ok.inj accepted⟩
  obtain ⟨codebook, generated, same⟩ := extract _ accepted
  subst prepared
  exact codebook_ambient generated

theorem ancestry_ambient {ambient : DataEnvironment} {layout : SourceCoreCallableIndexedAncestry.Layout}
    (accepted : SourceCoreCallableIndexedAncestry.Layout.prepare ambient = .ok layout) :
    layout.ambient = ambient := by
  unfold SourceCoreCallableIndexedAncestry.Layout.prepare at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

theorem layouts_ambient {initial : SourceCoreAllocationDiscovery.Prepared} {fuel : Nat} {expression : Expr}
    {discovered : SourceCoreAllocationDiscovery.Discovered initial fuel expression}
    {layouts : SourceCoreAllocationLayouts.Prepared}
    (accepted : SourceCoreAllocationLayouts.prepare discovered = .ok layouts) :
    layouts.codebook.ambient = initial.ambient := by
  unfold SourceCoreAllocationLayouts.prepare at accepted
  dsimp only at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · cases accepted
        exact codebook_ambient discovered.checked
      · cases accepted
    · cases accepted
  · cases accepted

/-- The actual final environment has exactly the catalog prefix, followed by
its actual indexed-frame definition and actual source marker definitions. -/
theorem definitions_exact {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    prepared.layouts.definitions = checked.catalog.definitions ++
      (prepared.ancestry.layout.frame.definition :: prepared.layouts.entries.map (·.layout.definition)) := by
  have layouts := layouts_ambient prepared.layoutsPrepared
  have discovery := discovery_ambient prepared.discoveryPrepared
  have ancestry := ancestry_ambient prepared.ancestry.layoutPrepared
  simp only [SourceCoreAllocationLayouts.Prepared.definitions, layouts, discovery,
    SourceCoreCallableIndexedAncestry.Layout.definitions, ancestry, List.append_assoc, List.singleton_append]

def ambientDefinitions {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    AmbientDefinitions checked.catalog.definitions where
  definitions := prepared.layouts.definitions
  basePrefix := ⟨_, definitions_exact prepared⟩

@[simp] theorem ambient_definitions {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    (ambientDefinitions prepared).definitions = prepared.layouts.definitions := rfl

theorem wellFormed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    (ambientDefinitions prepared).definitions.WellFormed := prepared.layouts.definitionsTyped

theorem base_constructor {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) {constructor : ConstructorId} {payload : Ty}
    (registered : checked.catalog.definitions.lookupConstructorPayloadType? constructor = some payload) :
    prepared.layouts.definitions.lookupConstructorPayloadType? constructor = some payload :=
  (ambientDefinitions prepared).basePrefix.constructor_lookup registered

/-- The frame is registered in the real final table independently of every
source metadata ID. Further allocation markers retain their owned indices. -/
theorem frame_registered {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    prepared.ancestry.layout.frame.Registered prepared.layouts.definitions := by
  have extension : prepared.ancestry.layout.definitions.Extends prepared.layouts.definitions := by
    refine ⟨prepared.layouts.entries.map (·.layout.definition), ?_⟩
    rw [SourceCoreAllocationLayouts.Prepared.definitions, layouts_ambient prepared.layoutsPrepared,
      discovery_ambient prepared.discoveryPrepared]
  exact ⟨extension.data_lookup prepared.ancestry.layout.registered.lookup⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
