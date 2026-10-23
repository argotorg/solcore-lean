import Solcore.Frontend.RustHull.AccountState
import Solcore.Frontend.RustHull.Creation
import Solcore.Frontend.RustHull.Calls

/-! CREATE/CREATE2 account lifecycle on ordinary Core. The enclosing runtime
provides checked constructor execution and exact deployed-image installation.
The creator nonce survives child failure; child world, balance and log changes
are restored together. Transaction-end deletion remains a separate operation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CreationRuntime
open Core CodeBuilder

private def response (address data size : Code) : Code := success (packet [address, data, size])
private def refused : Code := response (number 0) empty (number 0)

private def checkpoint (references : List Code) (continuation : Code → Code) : Code :=
  let rec capture : List Code → List (Code × Code) → Code
    | [], saved =>
        continuation (saved.foldr (fun (cell, value) next =>
          bind (store cell value) (fun _ => next)) unit)
    | reference :: rest, saved => bind (load reference) fun value =>
        capture rest ((reference, value) :: saved)
  capture references []

private def protect (restore attempt : Code) : Code := fun depth =>
  .caseE (attempt depth)
    ((bind restore fun _ => failure Creation.responseType
      (fun here => .var (here - depth - 1))) (depth + 1))
    (LanguageResult.success (.var 0))

private def deriveAddress (creator nonce request : Code) : Code :=
  choose (part 3 8 request)
    (bind (allocate WordMapping.type (part 6 8 request)) fun memory =>
      bind (allocate .word (number 0)) fun size =>
      fun depth => Creation.create2Address (memory depth) (size depth) (creator depth)
        (part 2 8 request depth) (number 0 depth) (part 7 8 request depth))
    (fun depth => Creation.createAddress (creator depth) (nonce depth))

private def transfer (balances creator target value creatorBalance : Code) : Code :=
  choose (binary .wordEq value (number 0)) (success unit) <|
  bindResult .unit (lookup (load balances) target) fun targetBalance =>
  choose (binary .wordGt targetBalance (binary .wordSub (number (wordModulus - 1)) value))
    (failure .unit (number 12)) <|
  bindResult .unit (insert (load balances) creator (binary .wordSub creatorBalance value)) fun debited =>
  bindResult .unit (insert debited target (binary .wordAdd targetBalance value)) fun credited =>
  success (store balances credited)

/-- Execute a creation request. `runInit target request` returns the usual
message-call response, while `installRuntime target childResponse` validates
and installs the exact returned runtime image. Both callbacks may mutate the
shared cells; every language failure is rolled back to the post-nonce snapshot.
Frame depth, static restrictions, gas and init-size limits are checked before
this dispatcher. All supplied references, completeness and request evaluate once. -/
def dispatch (worldReference balancesReference logsReference logSizeReference complete request : Code)
    (runInit : Code → Code → Code) (installRuntime : Code → Code → Code) : Code :=
  bind (packet [worldReference, balancesReference, logsReference, logSizeReference, complete, request]) fun args =>
  let world := part 0 6 args
  let balances := part 1 6 args
  let logs := part 2 6 args
  let logSize := part 3 6 args
  let complete := part 4 6 args
  let request := part 5 6 args
  let creator := address (part 0 8 request)
  let value := part 1 8 request
  bindResult Creation.responseType (lookup (load balances) creator) fun creatorBalance =>
  choose (binary .wordGt value creatorBalance) refused <|
  bindResult Creation.responseType (fun depth =>
    AccountState.get (load world depth) (creator depth) (complete depth)) fun creatorRecord =>
  let nonce := part 2 9 creatorRecord
  choose (binary .wordGt nonce (number (2 ^ 64 - 2))) refused <|
  bindResult Creation.responseType (deriveAddress creator nonce request) fun target =>
  bindResult Creation.responseType (fun depth => AccountState.writeField (world depth) (creator depth)
    (complete depth) 2 (binary .wordAdd nonce (number 1) depth)) fun _ =>
  checkpoint [world, balances, logs, logSize] fun restore =>
  let rollback (result : Code) := bind restore fun _ => result
  protect restore <|
  bindResult Creation.responseType (fun depth => AccountState.get (load world depth) (target depth)
    (complete depth)) fun existing =>
  choose (binary .wordGt (part 2 9 existing) (number 0)) refused <|
  choose (binary .wordGt (part 5 9 existing) (number 0)) refused <|
  choose (part 6 9 existing)
    (bindResult Creation.responseType (fun depth => AccountState.put (load world depth) (target depth)
      (AccountState.replace (AccountState.replace AccountState.defaultRecord 2 (number 1 depth)) 7 (.bool true))) fun inserted =>
      bind (store world inserted) fun _ =>
      bindResult Creation.responseType (transfer balances creator target value creatorBalance) fun _ =>
      bindResult Creation.responseType
        (choose (binary .wordEq (part 7 8 request) (number 0))
          (success (packet [boolean true, empty, number 0])) (runInit target request)) fun child =>
      choose (part 0 3 child)
        (choose (binary .wordGt (part 2 3 child) (number 24576)) (rollback refused) <|
          bindResult Creation.responseType (fun depth =>
            Memory.readMemoryByte (part 1 3 child depth) (number 0 depth)) fun first =>
          let invalidPrefix := choose (binary .wordGt (part 2 3 child) (number 0))
            (binary .wordEq first (number 0xef)) (boolean false)
          choose invalidPrefix (rollback refused) <|
          bindResult Creation.responseType (installRuntime target child) fun _ =>
          response target empty (number 0))
        (rollback (response (number 0) (part 1 3 child) (part 2 3 child))))
    (failure Creation.responseType (number 7))

end Solcore.Frontend.RustHull.CreationRuntime
