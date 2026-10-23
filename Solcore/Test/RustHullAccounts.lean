import Solcore.Frontend.RustHull.Contract

set_option autoImplicit false
namespace Tests.RustHullAccounts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Runtime" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}
private def branches (cases : List (Nat × List YulStmt)) : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0])
    (cases.map fun (value, body) => ⟨.number (toString value), body, none⟩)
    (some [action "invalid"]), none⟩]
private def defaultContext : Contract.Context := {
  address := word 0xaaa
  caller := word 0xbbb
  balance := word 100
  accounts := [(word 0xbbb, word 1000), (word 0xccc, word 5)]
  emptyAccounts := [word 0xccc]
  availableGas := some (word 100000)
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Prepared :=
  match Contract.prepare (source body) ["Runtime"] context with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8)
    (topics : List Nat := []) : IO Core.WordMapping.Entries := do
  let logs := topics.map fun topic => {address := word 0xaaa, topics := [word topic], data := [] : Logs.Event}
  require (receipt.logs == logs) s!"{label}: incorrect committed logs {reprStr receipt.logs}"
  match receipt.outcome with
  | .returned actual storage =>
      require (actual == expected) s!"{label}: unexpected bytes {reprStr actual}"
      pure storage
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def checkSlot (label : String) (entries : Core.WordMapping.Entries) (key expected : Nat) : IO Unit :=
  require (Core.WordMapping.lookupEntries (word key) entries == word expected)
    s!"{label}: wrong value at {key}"
private def emit (topic : Nat) : YulStmt := action "log1" [w 0, w 0, w topic]
private def selfCall (value : Nat := 0) : YulExpr :=
  call "call" [w 100000, call "address", w value, w 0, w 32, w 64, w 32]
private def send (target value : Nat) (gas : Nat := 100000) : YulExpr :=
  call "call" [w gas, w target, w value, w 0, w 0, w 0, w 0]
private def resumeUntil : Nat → Contract.Receipt → IO Contract.Receipt
  | 0, _ => throw (IO.userError "account resume budget exhausted")
  | fuel + 1, receipt => match receipt.outcome with
      | .outOfFuel state => do
          require (receipt.logs.isEmpty && receipt.balances.isEmpty) "suspended frame published a receipt"
          resumeUntil fuel (Contract.resumeWithReceipt state 5000)
      | _ => pure receipt

private def reentrantTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], action "tstore" [w 0, w 7], emit 10,
    action "mstore" [w 0, w 1], action "mstore" [w 128, selfCall 17], emit 30,
    action "mstore" [w 160, call "sload" [w 0]], action "mstore" [w 192, call "tload" [w 0]],
    action "mstore" [w 224, call "mload" [w 64]], action "mstore" [w 256, call "mload" [w 0]],
    action "return" [w 128, w 160]]
  let child := [action "sstore" [w 0, call "add" [call "sload" [w 0], w 1]],
    action "tstore" [w 0, call "add" [call "tload" [w 0], w 1]], emit 20,
    action "sstore" [w 1, call "caller"], action "sstore" [w 2, call "callvalue"],
    action "sstore" [w 3, call "selfbalance"],
    action "mstore" [w 0, call "sload" [w 0]], action "return" [w 0, w 32]]
  let prepared ← prepare "shared reentrant state" (branches [(0, outer), (1, child)])
  let expected := words [1, 12, 8, 12, 1]
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "reentrant writes and frame memory" receipt expected [10, 20, 30]
  checkSlot "outer update" storage 0 12
  checkSlot "child caller is current address" storage 1 0xaaa
  checkSlot "child receives value" storage 2 17
  checkSlot "self transfer keeps balance" storage 3 100
  checkSlot "self transfer receipt balance" receipt.balances 0xaaa 100
  let resumed ← resumeUntil 10000 (Contract.runWithReceipt prepared 100)
  let resumedStorage ← returned "reentrant call resumes" resumed expected [10, 20, 30]
  require (storage == resumedStorage && receipt.balances == resumed.balances)
    "resumption changed the committed world"
  let fresh ← prepare "transient storage resets at top-level entry"
    [action "mstore" [w 0, call "tload" [w 0]], action "return" [w 0, w 32]]
    {defaultContext with storage := storage}
  let _ ← returned "new top-level transient storage" (Contract.runWithReceipt fresh) (wordBytes 0)
  pure ()

private def rollbackTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], action "tstore" [w 0, w 7], emit 10,
    action "mstore" [w 0, w 1], action "mstore" [w 128, selfCall], emit 30,
    action "mstore" [w 160, call "sload" [w 0]], action "mstore" [w 192, call "tload" [w 0]],
    action "mstore" [w 224, call "returndatasize"], action "mstore" [w 256, call "mload" [w 64]],
    action "return" [w 128, w 160]]
  let child := [action "sstore" [w 0, w 99], action "tstore" [w 0, w 88], emit 20,
    action "pop" [send 0xccc 3], action "mstore" [w 0, w 2], action "pop" [selfCall],
    action "mstore" [w 0, w 0xabcdef], action "revert" [w 29, w 3]]
  let grandchild := [action "sstore" [w 0, w 123], action "tstore" [w 0, w 234], emit 25, action "stop"]
  let prepared ← prepare "nested successful grandchild then child revert"
    (branches [(0, outer), (1, child), (2, grandchild)])
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "child rollback retains parent changes" receipt
    (words [0, 11, 7, 3, 0xabcdef * 256 ^ 29]) [10, 30]
  checkSlot "storage checkpoint" storage 0 11
  checkSlot "sender balance checkpoint" receipt.balances 0xaaa 100
  checkSlot "recipient balance checkpoint" receipt.balances 0xccc 5
  let invalidChild := child.take (child.length - 2) ++ [action "invalid"]
  let prepared ← prepare "child invalid after nested success"
    (branches [(0, outer), (1, invalidChild), (2, grandchild)])
  let receipt := Contract.runWithReceipt prepared
  let storage ← returned "exceptional child rollback" receipt (words [0, 11, 7, 0, 0]) [10, 30]
  checkSlot "exceptional storage checkpoint" storage 0 11
  checkSlot "exceptional sender balance checkpoint" receipt.balances 0xaaa 100
  checkSlot "exceptional recipient balance checkpoint" receipt.balances 0xccc 5
  let successfulChild := [action "sstore" [w 0, w 77], emit 20, action "pop" [send 0xccc 3], action "stop"]
  let revertedOuter := [emit 10, action "mstore" [w 0, w 1], action "pop" [selfCall],
    action "revert" [w 0, w 0]]
  let prepared ← prepare "outer revert after successful child" (branches [(0, revertedOuter), (1, successfulChild)])
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "outer revert published nested effects"
  match receipt.outcome with
  | .reverted [] => pure ()
  | other => throw (IO.userError s!"outer revert: {reprStr other}")

private def balanceTests : IO Unit := do
  let body := [action "mstore" [w 0, send 0xccc 20], action "mstore" [w 32, send 0xccc 81],
    action "mstore" [w 64, call "selfbalance"], action "mstore" [w 96, call "returndatasize"],
    action "return" [w 0, w 128]]
  let prepared ← prepare "known empty recipient and insufficient funds" body
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "value transfers" receipt (words [1, 0, 80, 0])
  checkSlot "sender debit" receipt.balances 0xaaa 80
  checkSlot "recipient credit" receipt.balances 0xccc 25
  let unknown ← prepare "unknown account fails explicitly" [emit 10, action "pop" [send 0xddd 20], action "stop"]
  let receipt := Contract.runWithReceipt unknown
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "unsupported call published world changes"
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 7) "incorrect unknown-account failure"
  | other => throw (IO.userError s!"unknown account: {reprStr other}")
  let high := 2 ^ 200
  let canonical ← prepare "address canonicalization"
    [action "mstore" [w 0, call "address"], action "mstore" [w 32, call "caller"],
      action "mstore" [w 64, send (high + 0xccc) 20], action "return" [w 0, w 96]]
    {defaultContext with
      address := word (high + 0xaaa)
      caller := word (high + 0xbbb)
      emptyAccounts := [word (high + 0xccc)]
      accounts := [(word (high + 0xccc), word 5)]}
  let receipt := Contract.runWithReceipt canonical
  let _ ← returned "canonical frame and account addresses" receipt (words [0xaaa, 0xbbb, 1])
  checkSlot "canonical recipient" receipt.balances 0xccc 25

private def staticTests : IO Unit := do
  let outer := [action "sstore" [w 0, w 11], emit 10, action "mstore" [w 0, w 1],
    action "mstore" [w 128, call "staticcall" [w 100000, call "address", w 0, w 32, w 64, w 32]],
    emit 30, action "mstore" [w 160, call "sload" [w 0]], action "return" [w 128, w 64]]
  let attempts := [
    ("read", [action "mstore" [w 64, call "sload" [w 0]], action "return" [w 64, w 32]]),
    ("sstore", [action "sstore" [w 0, w 99]]),
    ("tstore", [action "tstore" [w 0, w 99]]),
    ("log", [emit 20]),
    ("value call", [action "pop" [send 0xccc 1]]),
    ("static inheritance through zero-value call", [action "mstore" [w 0, w 2],
      action "mstore" [w 64, selfCall], action "return" [w 64, w 32]])]
  for (label, operations) in attempts do
    let child := operations ++ [action "stop"]
    let prepared ← prepare s!"static {label}"
      (branches [(0, outer), (1, child), (2, [action "sstore" [w 0, w 99], action "stop"])])
    let receipt := Contract.runWithReceipt prepared
    -- The intermediate static child catches its descendant's exceptional halt.
    let status := if label == "read" || label == "static inheritance through zero-value call" then 1 else 0
    let storage ← returned s!"static {label}" receipt (words [status, 11]) [10, 30]
    checkSlot s!"static {label} unchanged storage" storage 0 11
    checkSlot s!"static {label} unchanged balance" receipt.balances 0xaaa 100
  let prepared ← prepare "top-level static violation" [action "sstore" [w 0, w 99]]
    {defaultContext with isStatic := true}
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "static failure published a receipt"
  match receipt.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"top-level static write: {reprStr other}")

private def precompileValueTests : IO Unit := do
  let identity := call "call" [w 18, w 4, w 10, w 0, w 3, w 64, w 3]
  let insufficientRecovery := call "call" [w 0, w 1, w 10, w 0, w 3, w 96, w 32]
  let body := [action "calldatacopy" [w 0, w 0, w 3],
    action "mstore" [w 128, identity], action "mstore" [w 160, insufficientRecovery],
    action "mstore" [w 192, call "returndatasize"], action "mstore" [w 224, call "selfbalance"],
    action "return" [w 128, w 128]]
  let prepared ← prepare "precompile value transfer and gas-failure rollback" body
    {defaultContext with calldata := "abc".toUTF8.toList, accounts := [(word 1, word 7), (word 4, word 2)]}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "precompile CALL" receipt (words [1, 0, 0, 90])
  checkSlot "successful precompile receives value" receipt.balances 4 12
  checkSlot "failed precompile keeps old balance" receipt.balances 1 7
  checkSlot "failed precompile refunds sender" receipt.balances 0xaaa 90

private def dispatchPriorityTests : IO Unit := do
  let constructor ← prepare "self code is unavailable during construction"
    [emit 10, action "mstore" [w 0, selfCall 5],
      action "mstore" [w 32, call "returndatasize"], action "mstore" [w 64, call "selfbalance"],
      action "return" [w 0, w 96]]
    {defaultContext with selfCodeAvailable := false}
  let receipt := Contract.runWithReceipt constructor
  let _ ← returned "constructor self call sees empty code" receipt (words [1, 0, 100]) [10]
  checkSlot "constructor self transfer" receipt.balances 0xaaa 100
  let precompile ← prepare "precompile wins over self-code selection"
    [action "calldatacopy" [w 0, w 0, w 3],
      action "mstore" [w 64, call "call" [w 18, call "address", w 0, w 0, w 3, w 96, w 3]],
      action "return" [w 64, w 35]]
    {defaultContext with address := word 4, calldata := "abc".toUTF8.toList}
  let receipt := Contract.runWithReceipt precompile
  let _ ← returned "precompile dispatch priority" receipt (wordBytes 1 ++ "abc".toUTF8.toList)
  checkSlot "precompile self transfer" receipt.balances 4 100

/-- Value-bearing calls include the protocol stipend in the explicit child budget. -/
def runValueStipend : IO Unit := do
  let prepared ← prepare "value CALL includes its stipend"
    [action "calldatacopy" [w 0, w 0, w 3],
      action "mstore" [w 128, call "call" [w 0, w 4, w 10, w 0, w 3, w 64, w 3]],
      action "return" [w 128, w 32]]
    {defaultContext with calldata := "abc".toUTF8.toList}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "zero requested gas can use the value stipend" receipt (wordBytes 1)
  checkSlot "stipend call transfers value" receipt.balances 4 10
  checkSlot "stipend call debits sender" receipt.balances 0xaaa 90
  let outer := [action "mstore" [w 0, w 1],
    action "mstore" [w 128, call "call" [w 0, call "address", w 1, w 0, w 32, w 64, w 32]],
    action "mstore" [w 160, call "mload" [w 64]], action "return" [w 128, w 64]]
  let child := [action "mstore" [w 0, call "gas"], action "return" [w 0, w 32]]
  let prepared ← prepare "child gas environment includes stipend" (branches [(0, outer), (1, child)])
  let _ ← returned "child receives stipend" (Contract.runWithReceipt prepared) (words [1, 2300])
  let prepared ← prepare "value stipend overflow is explicit"
    [emit 10, action "pop" [send 0xccc 1 (Core.wordModulus - 1)], action "stop"]
  let receipt := Contract.runWithReceipt prepared
  require (receipt.logs.isEmpty && receipt.balances.isEmpty) "stipend overflow published a receipt"
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 13) "incorrect stipend overflow reason"
  | other => throw (IO.userError s!"stipend overflow: {reprStr other}")

def runZeroValueLedger : IO Unit := do
  let prepared ← prepare "zero-value calls preserve the balance ledger"
    [action "mstore" [w 0, call "staticcall" [w 15, w 4, w 0, w 0, w 0, w 0]],
      action "mstore" [w 32, send 0xddd 0], action "return" [w 0, w 64]]
    {defaultContext with emptyAccounts := [word 0xddd]}
  let receipt := Contract.runWithReceipt prepared
  let _ ← returned "zero-value calls" receipt (words [1, 1])
  let expected := Core.WordMapping.insertEntries (word 0xaaa) (word 100) defaultContext.accounts
  require (receipt.balances == expected) "zero-value calls added ledger entries or changed balances"

def run : IO Unit := do
  reentrantTests
  rollbackTests
  balanceTests
  staticTests
  precompileValueTests
  dispatchPriorityTests
  runValueStipend
  runZeroValueLedger

end Tests.RustHullAccounts
