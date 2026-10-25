import Solcore.Frontend.RustHull.MemorySnapshotSemantics
import Solcore.Frontend.RustHull.RuntimeEffectsSemantics
import Solcore.Frontend.RustHull.AccountCallSemantics

/-! A completed child frame supplies its complete return or revert bytes.
Exceptional exits return false with empty data; ordinary language faults remain
faults for the enclosing account checkpoint. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ChildResultSemantics
open Core

def response (success : Bool) (size : Word) : Semantics.Result MemorySemantics.Entries → Semantics.Result AccountCallSemantics.Response
  | .value entries => .value ⟨success, entries, size⟩
  | .fault fault => .fault fault

inductive Respond (status : Semantics.Result Semantics.Value) (state : RuntimeEffectsSemantics.State) :
    Semantics.Result AccountCallSemantics.Response → Prop where
  | invalid (exit : state.storage.exit = Word.ofNatModulo 3) :
      Respond status state (.value (AccountCallSemantics.emptyResponse false))
  | reverted {data : Semantics.Result MemorySemantics.Entries}
      (exit : state.storage.exit = Word.ofNatModulo 2)
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      Respond status state (response false state.storage.returnSize data)
  | returned {data : Semantics.Result MemorySemantics.Entries}
      (exit : state.storage.exit = Word.ofNatModulo 1)
      (extracted : MemorySnapshotSemantics.Extract state.memory.words state.storage.returnOffset state.storage.returnSize data) :
      Respond status state (response true state.storage.returnSize data)
  | failed {fault : Semantics.Fault}
      (invalid : state.storage.exit ≠ Word.ofNatModulo 3)
      (reverted : state.storage.exit ≠ Word.ofNatModulo 2)
      (returned : state.storage.exit ≠ Word.ofNatModulo 1)
      (failed : status = .fault fault) : Respond status state (.fault fault)
  | completed
      (invalid : state.storage.exit ≠ Word.ofNatModulo 3)
      (reverted : state.storage.exit ≠ Word.ofNatModulo 2)
      (returned : state.storage.exit ≠ Word.ofNatModulo 1)
      (finished : status = .value .unit) :
      Respond status state (.value (AccountCallSemantics.emptyResponse true))

end Solcore.Frontend.RustHull.ChildResultSemantics
