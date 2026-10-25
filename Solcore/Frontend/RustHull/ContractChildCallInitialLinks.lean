import Solcore.Frontend.RustHull.CatalogWorldCorrespondence

/-! Initial code links are derived from ordinary source-world lookups and the
compiler's byte-image order. No runtime cell relation is a public premise. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContractChildCallCorrespondence

/-- Source accounts name their bytecode. The static image lookup records which
compiled catalog entry the actual initializer assigns to each linked account. -/
def InitialCatalogLinks (image : Option (List UInt8)) (catalog : List AccountRuntime.CodeDefinition)
    (anchors : List CatalogWorldCorrespondence.Anchor) (root : Core.Word) (world : StorageSemantics.World) : Prop :=
  ∀ anchor ∈ anchors, ∃ account,
    StorageSemantics.lookup anchor.address world = some account ∧
    account.code = some anchor.bytes ∧ anchor.address ≠ root ∧
    Contract.codeIdentity (image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
      (some anchor.bytes) = anchor.identity

theorem initial_links {image : Option (List UInt8)} {catalog : List AccountRuntime.CodeDefinition}
    {anchors : List CatalogWorldCorrespondence.Anchor} (object : Contract.CompiledObject) (context : Contract.Context)
    (images : object.codeImages = image :: catalog.map (some ∘ AccountRuntime.CodeDefinition.bytes))
    (source : InitialCatalogLinks image catalog anchors (Contract.normalizeAddress context.address)
      ((StorageCorrespondence.canonical (object.initialWorld context)).map Prod.fst)) :
    CatalogWorldCorrespondence.Links anchors (StorageCorrespondence.canonical (object.initialWorld context)) := by
  intro anchor member
  obtain ⟨account, selected, code, different, identity⟩ := source anchor member
  refine ⟨account, ?_, code⟩
  have found := CatalogWorldCorrespondence.initialWorld_lookup object context selected different
  simpa only [images, code, identity] using found

end Solcore.Frontend.RustHull.ContractChildCallCorrespondence
