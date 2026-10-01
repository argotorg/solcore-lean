import Solcore.Frontend.SourceCoreCallableIndexedTemplates
import Solcore.Frontend.SourceCoreCallableIndexedLedger

/-! Owned indexed callable provenance and source capture restoration.
Code authentication stays in IndexedTemplates. The profile-independent join
selects exact physical source rows and checks cached binder/type/owner/context.
Successful result provenance and failed/suspended heap provenance are separate. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedCaptures
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Cache {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedTemplates.Cache prepared
abbrev Authenticated {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (world : StoreTyping) (store : Store) (value : Value) := SourceCoreCallableIndexedTemplates.Authenticated cache world store value
abbrev Completion {checked : Checked} (prepared : Prepared checked) := SourceCoreCallableIndexedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceEnvironment := SourceCoreAllocationLedger.SourceEnvironment
abbrev TypedLedger := SourceCoreAllocationLedger.TypedLedger
abbrev Subvalue (value : Value) := SourceCoreCallableNativeSlots.Subvalue value
abbrev Error := SourceCoreCallableNativeCaptureJoin.Error

structure Produced {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) (world : StoreTyping) (store : Store) (value : Value) where private mk ::
  authenticated : Authenticated cache world store value
  result : Value
  observation : completion.result.native.observation = .succeeded result store
  subvalue : Subvalue value result

def Produced.of_success {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value result : Value}
    (authenticated : Authenticated cache world store value)
    (observation : completion.result.native.observation = .succeeded result store)
    (subvalue : Subvalue value result) : Produced cache completion world store value :=
  ⟨authenticated, result, observation, subvalue⟩

abbrev Slot {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store)
    (capture : SourceCoreCallableNativeCaptureJoin.Capture
      (SourceCoreCallableNativeCaptureJoin.ofTemplate authenticated.template) authenticated.environment world) :=
  SourceCoreCallableNativeCaptureJoin.Slot (contexts := prepared.contexts) ledger capture

/-- These are metadata/location facts. Produced or Stored retains the actual
owning completion; this receipt alone does not establish execution history. -/
structure Captured {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  environment : SourceEnvironment
  slots : SourceCoreCallableNativeCaptureJoin.CaptureSourceEnv (contexts := prepared.contexts)
    ledger authenticated.sourceCaptures environment

theorem Captured.related {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    {authenticated : Authenticated cache world store value} {initial : SourceHeap}
    {ledger : TypedLedger prepared.layouts initial world store} (captured : Captured authenticated ledger) :
    SourceCoreCallableNativeCaptureJoin.CaptureSourceEnv (contexts := prepared.contexts)
      ledger authenticated.sourceCaptures captured.environment := captured.slots

def joinAuthenticated {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : StoreTyping} {store : Store} {value : Value}
    (authenticated : Authenticated cache world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Captured authenticated ledger) := do
  let joined ← SourceCoreCallableNativeCaptureJoin.join (contexts := prepared.contexts) ledger authenticated.sourceCaptures
  pure ⟨joined.source, joined.related⟩

abbrev Receipt {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) := Captured produced.authenticated ledger

def join {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    (produced : Produced cache completion world store value) {initial : SourceHeap}
    (ledger : TypedLedger prepared.layouts initial world store) : Except Error (Receipt produced ledger) :=
  joinAuthenticated produced.authenticated ledger

/-- Heap payload provenance also covers failed and suspended invocations.
Only source ledger payloads are traversed, never an arbitrary closure's saved
Core environment or a compiler-only administrative cell. -/
structure Stored {checked : Checked} {prepared : Prepared checked} (cache : Cache prepared)
    (completion : Completion prepared) {world : StoreTyping} {store : Store} (value : Value)
    {initial : SourceHeap} (ledger : TypedLedger prepared.layouts initial world store) where private mk ::
  authenticated : Authenticated cache world store value
  observation : SourceCoreCallableIndexedLedger.store completion = store
  ordinal : Fin ledger.ledger.rows.length
  payload : Value
  payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload
  subvalue : Subvalue value payload

def Stored.of_payload {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value payload : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (authenticated : Authenticated cache world store value)
    (observation : SourceCoreCallableIndexedLedger.store completion = store)
    (ordinal : Fin ledger.ledger.rows.length)
    (payloadFound : (ledger.ledger.rows[ordinal]).payload = some payload)
    (subvalue : Subvalue value payload) : Stored cache completion value ledger :=
  ⟨authenticated, observation, ordinal, payload, payloadFound, subvalue⟩

def joinStored {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {completion : Completion prepared} {world : StoreTyping} {store : Store} {value : Value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (stored : Stored cache completion value ledger) : Except Error (Captured stored.authenticated ledger) :=
  joinAuthenticated stored.authenticated ledger

namespace Captured
variable {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
  {world : StoreTyping} {store : Store} {value : Value}
  {authenticated : Authenticated cache world store value} {initial : SourceHeap}
  {ledger : TypedLedger prepared.layouts initial world store}

theorem length (receipt : Captured authenticated ledger) :
    receipt.environment.length = authenticated.template.source.scope.length :=
  receipt.related.length.trans authenticated.capturesComplete

theorem binders (receipt : Captured authenticated ledger) :
    receipt.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := by
  have lengths := congrArg List.length authenticated.capturesExact
  simp only [List.length_map, List.length_zip, authenticated.capturesComplete] at lengths
  have enough : authenticated.template.source.scope.length ≤ authenticated.template.references.length := by omega
  have exact := congrArg (List.map (fun entry : Nat × (Resolved.LocalId × Ty) => entry.2.1))
    authenticated.capturesExact
  have captureOrder : authenticated.sourceCaptures.map (·.binder) =
      authenticated.template.source.scope.map Prod.fst := by
    have zipped : (authenticated.template.references.zip authenticated.template.source.scope).map
        (fun entry => entry.2.1) = authenticated.template.source.scope.map Prod.fst := by
      simpa only [List.map_map, Function.comp_def] using congrArg (List.map Prod.fst) (List.map_snd_zip enough)
    simpa only [List.map_map, Function.comp_def] using exact.trans zipped
  exact receipt.related.binders.trans captureOrder

theorem lookup (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    ∃ capture, authenticated.sourceCaptures[index]? = some capture ∧ capture.binder = binder ∧
      ∃ slot : Slot ledger capture, slot.sourceLocation = location := receipt.related.lookup found

theorem outsidePrefix (receipt : Captured authenticated ledger) {index : Nat} {binder : Resolved.LocalId}
    {location : SourceTypedRuntime.Location} (found : receipt.environment[index]? = some (binder, location)) :
    initial.length ≤ location.index := by
  obtain ⟨_, _, _, slot, same⟩ := receipt.lookup found
  rw [← same, slot.prefixOffset]
  omega

end Captured
end Solcore.Frontend.SourceCoreCallableIndexedCaptures
