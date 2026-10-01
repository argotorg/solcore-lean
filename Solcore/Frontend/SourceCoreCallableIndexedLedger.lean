import Solcore.Frontend.SourceCoreCallableIndexedPrograms
import Solcore.Frontend.SourceCoreCallableIndexedFrames
import Solcore.Frontend.SourceCoreCompatibleMarkedLedger

/-! The actual frame-aware runner's typed store and source allocation ledger.
The context cell remains administrative. Decoding its constant-depth carrier supplies
its exact shape, while ownership of the frame words and execution history
remain separate obligations. Observations never resume a checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedLedger
open Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableIndexedPrograms.Prepared
abbrev Completion {checked : Checked} (prepared : Prepared checked) :=
  SourceCoreCallableIndexedPrograms.Completion prepared
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap

def store {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : Store :=
  SourceCoreCompatibleMarkedLedger.observedStore completion.result.native.observation

def world {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) : StoreTyping :=
  (store completion).map Value.type

theorem store_typed {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    RuntimeStoreHasTypes (world completion) (store completion) prepared.layouts.definitions :=
  SourceCoreCompatibleMarkedLedger.native_store_typed completion.result.native

abbrev Receipt {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap) :=
  SourceCoreAllocationLedger.TypedLedger prepared.layouts initial (world completion) (store completion)

def scan {checked : Checked} {prepared : Prepared checked}
    (completion : Completion prepared) (initial : SourceHeap := []) :
    Except SourceCoreAllocationLedger.Error (Receipt completion initial) :=
  SourceCoreAllocationLedger.scanTyped prepared.layouts initial (world completion) (store completion)
    (store_typed completion)

/-- Public runSource starts with the fresh context cell at location zero. A
checkpoint taken before that allocation has no frame yet. -/
def frame? {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Option SourceCoreCallableIndexedFrames.Frame :=
  (store completion)[0]? >>= SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame

theorem frame_exact {checked : Checked} {prepared : Prepared checked} {completion : Completion prepared}
    {frame : SourceCoreCallableIndexedFrames.Frame} (decoded : frame? completion = some frame) :
    (store completion)[0]? = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame frame) := by
  unfold frame? at decoded
  cases selected : (store completion)[0]? with
  | none => simp [selected] at decoded
  | some value =>
      simp only [selected] at decoded
      exact congrArg some (SourceCoreCallableIndexedFrames.decode_sound _ value frame decoded)

/-- Lookup reads only the prepared finite table. This checks the scalar state
shape and range; actual ancestry history requires the emission proof boundary. -/
def state? {checked : Checked} {prepared : Prepared checked} (completion : Completion prepared) :
    Option (Option SourceCoreCallableAncestryPairedCache.State) :=
  frame? completion >>= SourceCoreCallableIndexedDispatch.lookup? prepared.ancestry.dispatch.table

end Solcore.Frontend.SourceCoreCallableIndexedLedger
