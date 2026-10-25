import Solcore.Frontend.RustHull.ContractChildCallInitialLinks

/-! Root reentry uses identity one from the actual public initializer. Other
accounts retain the image lookup policy, including aliases of the root image. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CatalogWorldCorrespondence
open Core StorageCorrespondence

/-- The first account is the current address, with the public storage, nonce
and code availability applied before canonical address normalization. -/
theorem initialWorld_root (object : Contract.CompiledObject) (context : Contract.Context) :
    ∃ account, lookup (Contract.normalizeAddress context.address)
        (canonical (object.initialWorld context)) =
        some (account, if context.selfCodeAvailable then 1 else 0) ∧
      account.code = (if context.selfCodeAvailable then object.codeImages.head?.getD none else some []) := by
  let current := {((context.world.find? (·.address == context.address)).getD
      {address := context.address}) with
    storage := context.storage, nonce := context.nonce
    code := if context.selfCodeAvailable then object.codeImages.head?.getD none else some []
    created := context.created}
  have address : current.address = context.address := by
    dsimp only [current]
    cases found : context.world.find? (·.address == context.address) with
    | none => rfl
    | some account =>
      have matched : (account.address == context.address) = true := List.find?_some (p := fun (entry : AccountState.Account) => entry.address == context.address) found
      exact beq_iff_eq.mp matched
  refine ⟨{current with address := Contract.normalizeAddress current.address}, ?_, rfl⟩
  change lookup (Contract.normalizeAddress context.address)
    (({current with address := Contract.normalizeAddress current.address},
      if current.address == context.address then (if context.selfCodeAvailable then 1 else 0)
      else Contract.codeIdentity object.codeImages current.code) :: _) = _
  simp only [lookup, address, beq_self_eq_true, ↓reduceIte]

/-- A supplied root image is assigned identity one without a catalog lookup. -/
theorem initialWorld_root_anchor (object : Contract.CompiledObject) (context : Contract.Context)
    {bytes : List UInt8}
    (available : context.selfCodeAvailable = true)
    (image : object.codeImages.head?.getD none = some bytes) :
    (Anchor.mk (Contract.normalizeAddress context.address) bytes 1).Holds
      (canonical (object.initialWorld context)) := by
  obtain ⟨account, found, code⟩ := initialWorld_root object context
  exact ⟨account, by simpa only [available, ↓reduceIte] using found,
    by simpa only [available, ↓reduceIte, image] using code⟩

theorem compiled_root_anchor {program : Program} {path : List String} {fuel : Nat}
    {bytes : List UInt8} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    (accepted : Contract.compileObject program path fuel (some bytes) catalog = .ok object)
    (context : Contract.Context) (available : context.selfCodeAvailable = true) :
    (Anchor.mk (Contract.normalizeAddress context.address) bytes 1).Holds
      (canonical (object.initialWorld context)) := by
  apply initialWorld_root_anchor object context available
  rw [compileObject_images accepted]
  rfl

end Solcore.Frontend.RustHull.CatalogWorldCorrespondence

namespace Solcore.Frontend.RustHull.ContractRootCallCorrespondence
open Core

/-- Source-side initial links permit the current root image and ordinary
catalog accounts. A non-root account may also carry identity one when its bytes
match the root image. Root code must actually be available in this context. -/
def InitialCatalogLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (anchors : List CatalogWorldCorrespondence.Anchor) (root : Word) (available : Bool)
    (world : StorageSemantics.World) : Prop :=
  ∀ anchor ∈ anchors,
    (anchor.address = root ∧ anchor.identity = 1 ∧ image = some anchor.bytes ∧ available = true) ∨
    (∃ account, StorageSemantics.lookup anchor.address world = some account ∧
      account.code = some anchor.bytes ∧ anchor.address ≠ root ∧
      Contract.codeIdentity (image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
        (some anchor.bytes) = anchor.identity)

theorem InitialCatalogLinks.of_catalog {image : Option (List UInt8)}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {root : Word} {world : StorageSemantics.World}
    (related : ContractChildCallCorrespondence.InitialCatalogLinks image catalog anchors root world)
    (available : Bool) : InitialCatalogLinks image catalog anchors root available world :=
  fun anchor member => Or.inr (related anchor member)

theorem InitialCatalogLinks.root_cons {bytes : List UInt8}
    {catalog : List AccountRuntime.CodeDefinition} {anchors : List CatalogWorldCorrespondence.Anchor}
    {root : Word} {world : StorageSemantics.World}
    (related : ContractChildCallCorrespondence.InitialCatalogLinks (some bytes) catalog anchors root world) :
    InitialCatalogLinks (some bytes) catalog (⟨root, bytes, 1⟩ :: anchors) root true world := by
  intro anchor member
  rcases List.mem_cons.mp member with rfl | member
  · exact .inl ⟨rfl, rfl, rfl, rfl⟩
  · exact .inr (related anchor member)

theorem initial_links {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor} (object : Contract.CompiledObject) (context : Contract.Context)
    (images : object.codeImages = image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
    (source : InitialCatalogLinks image catalog anchors (Contract.normalizeAddress context.address)
      context.selfCodeAvailable ((StorageCorrespondence.canonical (object.initialWorld context)).map Prod.fst)) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)) := by
  intro anchor member
  rcases source anchor member with ⟨address, identity, image, available⟩ | other
  · have held := CatalogWorldCorrespondence.initialWorld_root_anchor object context available (by rw [images]; exact image)
    rcases anchor with ⟨ownAddress, bytes, ownIdentity⟩
    cases address
    cases identity
    exact held
  · obtain ⟨account, selected, code, different, identity⟩ := other
    refine ⟨account, ?_, code⟩
    have found := CatalogWorldCorrespondence.initialWorld_lookup object context selected different
    simpa only [images, code, identity] using found

/-- The condition is checked against the same normalized source accounts used
by public execution; it contains no Core store or execution assumption. -/
def InitialContextLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (object : Contract.CompiledObject) (context : Contract.Context)
    (anchors : List CatalogWorldCorrespondence.Anchor) : Prop :=
  let normalized := Contract.normalizeContext context
  InitialCatalogLinks image catalog anchors (Contract.normalizeAddress normalized.address)
    normalized.selfCodeAvailable ((StorageCorrespondence.canonical (object.initialWorld normalized)).map Prod.fst)

theorem initial_context_links {program : Program} {path : List String} {fuel : Nat}
    {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition} {object : Contract.CompiledObject}
    {anchors : List CatalogWorldCorrespondence.Anchor}
    (accepted : Contract.compileObject program path fuel image catalog = .ok object)
    (context : Contract.Context) (source : InitialContextLinks image catalog object context anchors) :
    CatalogWorldCorrespondence.Links anchors
      (StorageCorrespondence.canonical (object.initialWorld (Contract.normalizeContext context))) :=
  initial_links object (Contract.normalizeContext context) (CatalogWorldCorrespondence.compileObject_images accepted) source

end Solcore.Frontend.RustHull.ContractRootCallCorrespondence
