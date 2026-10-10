import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionEntries

/-! The named owner comes from the actual prepared bootstrap. Its zero
capture prefix is the literal key produced by initialization. An immutable
key embedding retains that complete key when the domain grows. Source
headers and their real cache ledger remain independent static inputs. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory RecursiveNamedCatalog
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey KeyEmbedding NamedCapture)
open CallableIndexedOwnedFunctionEntries (OwnedPool)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (Header compiled program)}

/-- This packet keeps the actual initialization authority and its static
recipe receipts. It contains no assumed capture-prefix equality. -/
structure Bootstrap
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) (world : StoreTyping) where
  recipe : SourceCoreIndexedSession.Recipe
  accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe
  ledger : Ledger headers compiled.indexed.secondPass.closures
  sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length
  locals : ∀ header, header ∈ headers → header.function.context.locals = []
  heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions [] world ⟨[]⟩
    (RecursiveNamedCatalogPreparedInitialization.store compiled)
  entry : Entry (prepared := compiled.indexed.ancestry)
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    headers
    (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
    0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
    (RecursiveNamedCatalogPreparedInitialization.environment compiled)

namespace Bootstrap

variable {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping}

def key (packet : Bootstrap (headers := headers) functions registry world) : Key compiled program :=
  ⟨(fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot),
    0, packet.entry.authority.frameLocation⟩

def keys (packet : Bootstrap (headers := headers) functions registry world) : List (Key compiled program) :=
  [packet.key]

def owner (packet : Bootstrap (headers := headers) functions registry world) : OwnedKey packet.keys :=
  ⟨⟨0, by simp [keys]⟩⟩

theorem owner_key (packet : Bootstrap (headers := headers) functions registry world) :
    packet.owner.key = packet.key := by
  rfl

theorem capture_zero (packet : Bootstrap (headers := headers) functions registry world) :
    packet.owner.key.capturePrefix = 0 := by
  rfl

/-- The original singleton producer retains the same complete authority. -/
def pool (packet : Bootstrap (headers := headers) functions registry world) :
    OwnedPool headers packet.keys [] world ⟨[]⟩
      (RecursiveNamedCatalogPreparedInitialization.store compiled) :=
  CallableIndexedAuthorityPool.Pool.singleton
    (CallableIndexedAuthorityPool.EntryValid.of_authority packet.entry.authority)

theorem frame_read (packet : Bootstrap (headers := headers) functions registry world) :
    (RecursiveNamedCatalogPreparedInitialization.store compiled).read? packet.owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame
        (packet.pool.rows packet.owner.position).authority.current) :=
  CallableIndexedOwnedFunctionEntries.reached_frame_read packet.pool packet.owner.position

theorem global_locations (packet : Bootstrap (headers := headers) functions registry world)
    (header : Header compiled program) :
    packet.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rfl

/-- Both the capture and installed-code witness come from the same live
bootstrap row. The cache ledger identifies the actual emitted full closure. -/
theorem named_capture (packet : Bootstrap (headers := headers) functions registry world)
    {header : Header compiled program} (member : header ∈ headers) :
    ∃ capture : NamedCapture headers packet.owner.key header [] world,
      CallableIndexedOwnedFunctionValues.NamedInstalledCode capture := by
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool
    packet.pool packet.owner member
  refine ⟨NamedCapture.of_capture capture, ?_⟩
  exact CallableIndexedOwnedFunctionValues.NamedInstalledCode.of_bootstrap capture
    (packet.global_locations header) (packet.ledger.cached header member)

end Bootstrap

/-- Invoke the actual bootstrap entry factory once. Source inventory facts
are retained alongside that returned state; no arbitrary named capture is
upgraded to an initialization packet. -/
theorem of_recipe {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    (ledger : Ledger headers compiled.indexed.secondPass.closures)
    (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
    (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ world, Nonempty (Bootstrap (headers := headers) functions registry world) := by
  obtain ⟨world, heaps, ⟨entry⟩⟩ :=
    RecursiveNamedCatalogPreparedInitialization.entry compiled
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers ledger sizes locals
      accepted rfl functions registry
  exact ⟨world, ⟨⟨recipe, accepted, ledger, sizes, locals, heaps, entry⟩⟩⟩

/-- Positive named-owner provenance. The selected owner is defined by the
real bootstrap token and a complete immutable-key embedding. -/
structure NamedOwner (keys : List (Key compiled program))
    (functions : FunctionModel compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
    (registry : SourceCoreRawMetadata.Registry) where
  world : StoreTyping
  bootstrap : Bootstrap (headers := headers) functions registry world
  embedding : KeyEmbedding bootstrap.keys keys

namespace NamedOwner

variable {keys : List (Key compiled program)}
  {functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry : SourceCoreRawMetadata.Registry}

def owner (packet : NamedOwner (headers := headers) keys functions registry) : OwnedKey keys :=
  packet.embedding.map packet.bootstrap.owner

def of_bootstrap {world : StoreTyping}
    (packet : Bootstrap (headers := headers) functions registry world)
    (embedding : KeyEmbedding packet.keys keys) :
    NamedOwner (headers := headers) keys functions registry :=
  ⟨world, packet, embedding⟩

theorem key_eq (packet : NamedOwner (headers := headers) keys functions registry) :
    packet.owner.key = packet.bootstrap.owner.key :=
  packet.embedding.same packet.bootstrap.owner

theorem capture_zero (packet : NamedOwner (headers := headers) keys functions registry) :
    packet.owner.key.capturePrefix = 0 := by
  rw [packet.key_eq]
  exact packet.bootstrap.capture_zero

theorem globals (packet : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled program} (member : header ∈ headers) :
    header.globals = compiled.indexed.base.globals.length :=
  packet.bootstrap.sizes header member

theorem global_locations (packet : NamedOwner (headers := headers) keys functions registry)
    (header : Header compiled program) :
    packet.owner.key.locations header =
      RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot := by
  rw [packet.key_eq]
  exact packet.bootstrap.global_locations header

/-- Retain the same bootstrap capture through the whole-key embedding. This
does not infer bootstrap provenance from an arbitrary reached capture. -/
theorem named_capture (packet : NamedOwner (headers := headers) keys functions registry)
    {header : Header compiled program} (member : header ∈ headers) :
    ∃ capture : NamedCapture headers packet.owner.key header [] packet.world,
      CallableIndexedOwnedFunctionValues.NamedInstalledCode capture := by
  obtain ⟨capture, installed⟩ := packet.bootstrap.named_capture member
  let changed := capture.rekey packet.key_eq
  refine ⟨changed, ?_⟩
  simpa only [CallableIndexedOwnedFunctionValues.NamedInstalledCode, changed,
    NamedCapture.rekey_embedding] using installed

end NamedOwner
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedNamedBootstrapReceipts
