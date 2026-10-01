import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
import Solcore.Frontend.SourceCoreAllocationLedger

/-! Typed allocation-ledger observations of the actual marked compiler's Core
results. Success, language failure and suspension all expose their actual
store, typed in its canonical finite world under the artifact's definitions.
Suspension is retained as a checkpoint; observing it does not resume execution.

The supplied initial source heap remains an opaque prefix. This adapter does
not decode native payloads, authenticate arbitrary stores as execution traces,
or assert source evaluation correspondence. Its completion argument retains
the two real compiler receipts and the native result typing. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleMarkedLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCompatibleMarkedFunctions.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap

def observedStore : LanguageResult.Observation → Store
  | .succeeded _ store | .failed _ store | .invalidCarrier _ store => store
  | .outOfFuel state | .internalFault _ state => state.store

private theorem canonical_store {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions) :
    RuntimeStoreHasTypes (store.map Value.type) store definitions := by
  rw [← typed.world_eq]
  exact typed

theorem native_store_typed {definitions : DataEnvironment} {type : Ty}
    (result : SourceCoreGeneralEntry.Result definitions type) :
    RuntimeStoreHasTypes ((observedStore result.observation).map Value.type)
      (observedStore result.observation) definitions := by
  have typed := result.typed
  cases outcome : result.observation with
  | succeeded value store =>
    rw [outcome] at typed
    exact canonical_store typed.choose_spec.1
  | failed reason store =>
    rw [outcome] at typed
    obtain ⟨world, stored⟩ := typed
    exact canonical_store stored
  | outOfFuel state =>
    rw [outcome] at typed
    cases typed with
    | eval stored _ _ _ => exact canonical_store stored
    | ret stored _ _ => exact canonical_store stored
  | internalFault error state =>
    exact False.elim (result.ne_internalFault error state outcome)
  | invalidCarrier value store =>
    exact False.elim (result.ne_invalidCarrier value store outcome)

def store {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : Store :=
  observedStore completion.result.native.observation

def world {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : StoreTyping :=
  (store completion).map Value.type

theorem store_typed {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  native_store_typed completion.result.native

abbrev Receipt {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap) :=
  SourceCoreAllocationLedger.TypedLedger prepared.layouts initial (world completion) (store completion)

def scan {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap := []) :
    Except SourceCoreAllocationLedger.Error (Receipt completion initial) :=
  SourceCoreAllocationLedger.scanTyped prepared.layouts initial (world completion) (store completion)
    (store_typed completion)

theorem succeeded_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {value : Value} {actual : Store}
    (success : completion.result.native.observation = .succeeded value actual) : store completion = actual := by
  simp only [store, success, observedStore]

theorem failed_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {reason : Word} {actual : Store}
    (failure : completion.result.native.observation = .failed reason actual) : store completion = actual := by
  simp only [store, failure, observedStore]

theorem suspended_store {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) {checkpoint : State}
    (suspended : completion.result.native.observation = .outOfFuel checkpoint) :
    store completion = checkpoint.store := by
  simp only [store, suspended, observedStore]

theorem receipt_prefix {checked : Checked} {prepared : Prepared checked}
    {completion : Completion prepared} {initial : SourceHeap} (receipt : Receipt completion initial)
    {ε : Type} (decode : SourceCoreAllocationLedger.Row prepared.layouts (store completion) →
      Except ε SourceTypedRuntime.Cell) {heap : SourceHeap}
    (exported : receipt.ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial :=
  receipt.ledger.exportHeap_prefix decode exported

end Solcore.Frontend.SourceCoreCompatibleMarkedLedger
