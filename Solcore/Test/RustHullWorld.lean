import Solcore.Frontend.RustHull.LinkedContract
import Solcore.Abi.Keccak256

set_option autoImplicit false
namespace Tests.RustHullWorld
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ident (value : String) : YulExpr := ⟨.ident ⟨value, none⟩, none⟩
private def call (name : String) (args : List YulExpr := []) : YulExpr := ⟨.call ⟨name, none⟩ args, none⟩
private def action (name : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call name args), none⟩
private def letVar (name : String) (value : YulExpr) : YulStmt := ⟨.letDecl [⟨name, none⟩] (some value), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def bytesNat (bytes : List UInt8) : Nat := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
private def hex (text : String) : List UInt8 :=
  let digit (char : Char) := if char ≤ '9' then char.toNat - '0'.toNat else char.toNat - 'a'.toNat + 10
  (List.range (text.length / 2)).map fun index =>
    UInt8.ofNat (16 * digit text.toList[2 * index]! + digit text.toList[2 * index + 1]!)
-- Exact solc0.8.35 Osaka bytes from EvmAccounts/Target.yul and observations.json.
private def targetCode : List UInt8 := hex
  "5f3580600114604657806002146039576003146034575b305f523360205234604052600754606052476080523860a05260c05ff35b602035ff5b63deadbeef5f526004601cfd5b50602035600755601656"
private def initCode : List UInt8 := hex
  "6063600755303b600855303f60095560518060195f395ff3fe5f3580600114604657806002146039576003146034575b305f523360205234604052600754606052476080523860a05260c05ff35b602035ff5b63deadbeef5f526004601cfd5b50602035600755601656"
private def revertCode : List UInt8 := hex "63deadbeef5f526004601cfd"
private def targetBody : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0]) [
      ⟨.number "1", [action "sstore" [w 7, call "calldataload" [w 32]]], none⟩,
      ⟨.number "2", [action "sstore" [w 7, call "calldataload" [w 32]],
        action "mstore" [w 0, w 0xdeadbeef], action "revert" [w 28, w 4]], none⟩,
      ⟨.number "3", [action "selfdestruct" [call "calldataload" [w 32]]], none⟩] none, none⟩] ++
    ([call "address", call "caller", call "callvalue", call "sload" [w 7],
      call "selfbalance", call "codesize"].zipIdx.map fun (value, index) =>
        action "mstore" [w (32 * index), value]) ++ [action "return" [w 0, w 192]]
private def initBody : List YulStmt :=
  [action "sstore" [w 7, w 99], action "sstore" [w 8, call "extcodesize" [call "address"]],
   action "sstore" [w 9, call "extcodehash" [call "address"]],
   action "codecopy" [w 0, w 25, w 81], action "return" [w 0, w 81]]
private def source (body : List YulStmt) : Program := {
  objects := [.object "Object" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
  functions := []
  entryPoints := []
}
private def catalog : List AccountRuntime.CodeDefinition := [
  ⟨source targetBody, ["Object"], targetCode, false⟩,
  ⟨source initBody, ["Object"], initCode, true⟩,
  ⟨source [action "mstore" [w 0, w 0xdeadbeef], action "revert" [w 28, w 4]],
    ["Object"], revertCode, true⟩]
private def defaultContext : Contract.Context := {
  storage := [(word 7, word 10)]
  address := word 0xaaa
  caller := word 0xbbb
  balance := word 1000
  accounts := [(word 0xccc, word 1111), (word 0xddd, word 5)]
  emptyAccounts := [word 0xddd]
  world := [{
    address := word 0xccc
    code := some targetCode
    nonce := word 1
    storage := [(word 7, word 99)]
  }]
  availableGas := some (word 30000000)
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Prepared := do
  match Contract.compileObject (source body) ["Object"] 4096 (some [0x00]) catalog with
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
  | .ok compiled => pure (compiled.instantiate context)
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8) : IO Unit := do
  match receipt.outcome with
  | .returned bytes _ =>
      require (bytes == expected)
        s!"{label}: unexpected output {reprStr bytes}; expected {reprStr expected}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (label : String) (receipt : Contract.Receipt) (address : Nat) : IO AccountState.Account :=
  match receipt.world.find? (·.address == word address) with
  | some value => pure value
  | none => throw (IO.userError s!"{label}: missing account {address}")
private def slot (account : AccountState.Account) (key : Nat) : Core.Word :=
  Core.WordMapping.lookupEntries (word key) account.storage
private def balance (receipt : Contract.Receipt) (address : Nat) : Core.Word :=
  Core.WordMapping.lookupEntries (word address) receipt.balances
private def execute (label : String) (body : List YulStmt) (context : Contract.Context := defaultContext) :
    IO Contract.Receipt := do
  pure (Contract.runWithReceipt (← prepare label body context))

private def reportCall (operation : String) (value mode argument : Nat) (target : Nat := 0xccc) : List YulStmt :=
  let args := if operation == "call" || operation == "callcode" then
    [w 1000000, w target, w value, w 0, w 64, w 0, w 0]
    else [w 1000000, w target, w 0, w 64, w 0, w 0]
  [action "mstore" [w 0, w mode], action "mstore" [w 32, w argument],
   letVar "ok" (call operation args), letVar "size" (call "returndatasize"),
   action "mstore" [w 0, ident "ok"], action "mstore" [w 32, ident "size"],
   action "returndatacopy" [w 64, w 0, ident "size"],
   action "mstore" [call "add" [w 64, ident "size"], call "sload" [w 7]],
   action "mstore" [call "add" [w 96, ident "size"], call "selfbalance"],
   action "return" [w 0, call "add" [w 128, ident "size"]]]

private def callTests : IO Unit := do
  let receipt ← execute "delegate context" (reportCall "delegatecall" 0 1 77)
    {defaultContext with value := word 13, balance := word 1013}
  returned "delegate context" receipt (words [1, 192, 0xaaa, 0xbbb, 13, 77, 1013, 81, 77, 1013])
  require (slot (← account "delegate" receipt 0xaaa) 7 == word 77 &&
    slot (← account "delegate" receipt 0xccc) 7 == word 99) "delegate storage ownership"
  let receipt ← execute "callcode context" (reportCall "callcode" 17 1 88)
    {defaultContext with value := word 5, balance := word 1005}
  returned "callcode context" receipt (words [1, 192, 0xaaa, 0xaaa, 17, 88, 1005, 81, 88, 1005])
  require (balance receipt 0xccc == word 1111) "callcode transferred funds"
  let receipt ← execute "external call context" (reportCall "call" 17 1 77)
  returned "external call context" receipt (words [1, 192, 0xccc, 0xaaa, 17, 77, 1128, 81, 10, 983])
  require (slot (← account "call" receipt 0xccc) 7 == word 77 &&
    slot (← account "call" receipt 0xaaa) 7 == word 10) "call storage ownership"
  let receipt ← execute "insufficient callcode funds" (reportCall "callcode" 1001 1 55)
  returned "insufficient callcode funds" receipt (words [0, 0, 10, 1000])
  let receipt ← execute "delegate revert" (reportCall "delegatecall" 0 2 123)
  returned "delegate revert" receipt (words [0, 4] ++ hex "deadbeef" ++ words [10, 1000])
  require (slot (← account "reverted delegate" receipt 0xaaa) 7 == word 10) "delegate rollback"
  let receipt ← execute "static rejects write" (reportCall "staticcall" 0 1 42)
  returned "static rejects write" receipt (words [0, 0, 10, 1000])
  let receipt ← execute "static allows nonzero callcode" (reportCall "callcode" 17 0 0)
    {defaultContext with isStatic := true}
  returned "static allows nonzero callcode" receipt
    (words [1, 192, 0xaaa, 0xaaa, 17, 10, 1000, 81, 10, 1000])
  let receipt ← execute "known empty transfer" (reportCall "call" 3 0 0 0xddd)
  returned "known empty transfer" receipt (words [1, 0, 10, 997])
  require (balance receipt 0xddd == word 8) "empty recipient balance"
  let receipt ← execute "unknown executable image" (reportCall "call" 0 0 0)
    {defaultContext with world := [{address := word 0xccc, code := some [0x01], nonce := word 1}]}
  match receipt.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "unknown code failure reason"
  | other => throw (IO.userError s!"unknown code: {reprStr other}")
  require (receipt.world.isEmpty && receipt.balances.isEmpty && receipt.logs.isEmpty)
    "failed top-level call published account state"

private def writeMemory (bytes : List UInt8) : List YulStmt :=
  (List.range ((bytes.length + 31) / 32)).map fun index =>
    let chunk := (bytes.drop (32 * index)).take 32
    action "mstore" [w (32 * index), w (bytesNat (chunk ++ List.replicate (32 - chunk.length) 0))]
private def creation (two : Bool := false) (value : Nat := 17) (bytes : List UInt8 := initCode) : YulExpr :=
  if two then call "create2" [w value, w 0, w bytes.length, w 12345]
  else call "create" [w value, w 0, w bytes.length]
private def createBody (two : Bool := false) (bytes : List UInt8 := initCode) : List YulStmt :=
  writeMemory bytes ++ [letVar "child" (creation two 17 bytes),
    action "mstore" [w 0, ident "child"], action "mstore" [w 32, call "returndatasize"],
    action "mstore" [w 64, call "extcodesize" [ident "child"]],
    action "mstore" [w 96, call "extcodehash" [ident "child"]],
    action "return" [w 0, w 128]]
private def codeHash : Nat := bytesNat (Solcore.Abi.V1.Keccak256.hash targetCode.toByteArray).data.toList
private def createdAddress : Nat := 0x728c6cac8afdd93c35e798933d8d71a363fc4b4f
private def created2Address : Nat := bytesNat
  ((Solcore.Abi.V1.Keccak256.hash (([0xff] ++ (wordBytes 0xaaa).drop 12 ++ wordBytes 12345 ++
    (Solcore.Abi.V1.Keccak256.hash initCode.toByteArray).data.toList).toByteArray)).data.toList.drop 12)

private def creationTests : IO Unit := do
  let context := {defaultContext with completeWorld := true}
  let receipt ← execute "create public execution" (createBody) context
  returned "create public execution" receipt (words [createdAddress, 0, 81, codeHash])
  let child ← account "create" receipt createdAddress
  require (child.code == some targetCode && child.nonce == word 1 && slot child 7 == word 99)
    "created account image or persistent state"
  require (slot child 8 == word 0 && slot child 9 ==
    word 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)
    "constructing account exposed its code"
  require (!child.created && !child.destroyed && child.transient.isEmpty) "transaction flags escaped receipt"
  require ((← account "creator" receipt 0xaaa).nonce == word 2 &&
    balance receipt 0xaaa == word 983 && balance receipt createdAddress == word 17) "creation ledger/nonce"
  let collision := writeMemory initCode ++ [letVar "first" (creation true), letVar "second" (creation true 0),
    action "mstore" [w 0, ident "first"], action "mstore" [w 32, ident "second"], action "return" [w 0, w 64]]
  let receipt ← execute "create2 collision" collision context
  returned "create2 collision" receipt (words [created2Address, 0])
  require ((← account "create2 creator" receipt 0xaaa).nonce == word 3) "collision nonce increment"
  let reverted := writeMemory revertCode ++ [letVar "child" (creation false 17 revertCode),
    action "mstore" [w 0, ident "child"], action "mstore" [w 32, call "returndatasize"],
    action "returndatacopy" [w 64, w 0, w 4], action "return" [w 0, w 68]]
  let receipt ← execute "reverted constructor" reverted context
  returned "reverted constructor" receipt (words [0, 4] ++ hex "deadbeef")
  require ((← account "failed creator" receipt 0xaaa).nonce == word 2 && balance receipt 0xaaa == word 1000)
    "constructor failure lost nonce or retained transfer"
  require (!(receipt.world.any (·.address == word createdAddress))) "failed constructor account survived"
  let parentReverts := writeMemory initCode ++ [action "pop" [creation], action "revert" [w 0, w 0]]
  let receipt ← execute "parent reverts creation" parentReverts context
  match receipt.outcome with
  | .reverted [] => require (receipt.world.isEmpty && receipt.balances.isEmpty) "reverted parent published child"
  | other => throw (IO.userError s!"parent creation rollback: {reprStr other}")

private def destructionTests : IO Unit := do
  let receipt ← execute "existing selfdestruct" (reportCall "call" 0 3 0xddd)
  returned "existing selfdestruct" receipt (words [1, 0, 10, 1000])
  let target ← account "existing destruction" receipt 0xccc
  require (target.code == some targetCode && slot target 7 == word 99 && target.nonce == word 1)
    "existing selfdestruct deleted persistent state"
  require (balance receipt 0xccc == word 0 && balance receipt 0xddd == word 1116) "selfdestruct transfer"
  let receipt ← execute "existing self-beneficiary" (reportCall "call" 0 3 0xccc)
  returned "existing self-beneficiary" receipt (words [1, 0, 10, 1000])
  require (balance receipt 0xccc == word 1111) "existing self-beneficiary burned funds"
  let receipt ← execute "static selfdestruct" (reportCall "staticcall" 0 3 0xddd)
  returned "static selfdestruct" receipt (words [0, 0, 10, 1000])
  require (balance receipt 0xccc == word 1111) "static selfdestruct transferred funds"
  for selfBeneficiary in [false, true] do
    let recipient := if selfBeneficiary then ident "child" else w 0xddd
    let body := writeMemory initCode ++ [letVar "child" (creation true),
      action "mstore" [w 0, w 3], action "mstore" [w 32, recipient],
      letVar "ok" (call "call" [w 1000000, ident "child", w 0, w 0, w 64, w 0, w 0]),
      letVar "size" (call "extcodesize" [ident "child"]),
      letVar "hash" (call "extcodehash" [ident "child"])] ++ writeMemory initCode ++
      [letVar "again" (creation true 0), action "mstore" [w 0, ident "ok"],
       action "mstore" [w 32, ident "size"], action "mstore" [w 64, ident "hash"],
       action "mstore" [w 96, ident "again"], action "return" [w 0, w 128]]
    let receipt ← execute "created selfdestruct" body {defaultContext with completeWorld := true}
    returned "created selfdestruct" receipt (words [1, 81, codeHash, 0])
    require (!(receipt.world.any (·.address == word created2Address))) "created destroyed account survived finalization"
    require (balance receipt 0xddd == word (if selfBeneficiary then 5 else 22) &&
      balance receipt 0xaaa == word 983) "created destruction balance semantics"

private def hostWorldTests : IO Unit := do
  let alias := 2 ^ 200
  let context := {defaultContext with
    address := word (alias + 0xaaa)
    caller := word (alias + 0xbbb)
    emptyAccounts := [word (alias + 0xccc), word 0xccc, word (alias + 0xddd), word 0xddd]
    world := [
      {address := word (alias + 0xccc), code := some targetCode, created := true, destroyed := true},
      {address := word 0xccc, nonce := word 19, code := some targetCode},
      {address := word (alias + 0xaaa), nonce := word 20, storage := [(word 7, word 55)]},
      {address := word 0xaaa, nonce := word 21}]}
  let receipt ← execute "host normalizes duplicate account aliases"
    [action "mstore" [w 0, call "address"], action "mstore" [w 32, call "caller"],
     action "mstore" [w 64, call "sload" [w 7]], action "return" [w 0, w 96]] context
  returned "host normalizes duplicate account aliases" receipt (words [0xaaa, 0xbbb, 10])
  require (!(receipt.world.any (·.address == word 0xccc)))
    "finalization exposed a duplicate account after deleting its first alias"
  require ((← account "current account overrides aliases" receipt 0xaaa).nonce == word 1)
    "current account nonce did not override supplied aliases"
  let addresses := receipt.world.map AccountState.Account.address
  require (addresses.length == addresses.eraseDups.length && addresses.all (·.val < 2 ^ 160))
    "world receipt contains duplicate or noncanonical account addresses"

private def continuationTests : IO Unit := do
  let prepared ← prepare "creation suspension" createBody {defaultContext with completeWorld := true}
  let suspended := Contract.runWithReceipt prepared 1000
  let receipt ← match suspended.outcome with
    | .outOfFuel state =>
        require (suspended.world.isEmpty && suspended.balances.isEmpty && suspended.logs.isEmpty)
          "suspended transaction published partial account state"
        pure (Contract.resumeWithReceipt state)
    | other => throw (IO.userError s!"creation should suspend: {reprStr other}")
  returned "creation resumes with world references" receipt (words [createdAddress, 0, 81, codeHash])
  let creator ← account "resumed creator" receipt 0xaaa
  let next := {defaultContext with
    world := receipt.world, accounts := receipt.balances, storage := creator.storage,
    nonce := creator.nonce, balance := balance receipt 0xaaa, completeWorld := true}
  let nextReceipt ← execute "created image executes in a later transaction"
    (reportCall "call" 0 1 123 createdAddress) next
  returned "created image executes in a later transaction" nextReceipt
    (words [1, 192, createdAddress, 0xaaa, 0, 123, 17, 81, 10, 983])
  require (slot (← account "persisted child" nextReceipt createdAddress) 7 == word 123 &&
    (← account "persisted nonce" nextReceipt 0xaaa).nonce == word 2)
    "receipt replay lost child storage or creator nonce"
  let creator ← account "creator before later destruction" nextReceipt 0xaaa
  let finalContext := {next with
    world := nextReceipt.world, accounts := nextReceipt.balances, storage := creator.storage,
    nonce := creator.nonce, balance := balance nextReceipt 0xaaa}
  let finalReceipt ← execute "previously created child is now an existing account"
    (reportCall "call" 0 3 0xddd createdAddress) finalContext
  returned "previously created child is now an existing account" finalReceipt (words [1, 0, 10, 983])
  require ((← account "child survives later selfdestruct" finalReceipt createdAddress).code == some targetCode &&
    balance finalReceipt createdAddress == word 0 && balance finalReceipt 0xddd == word 22)
    "created flag incorrectly survived a public transaction boundary"

def run : IO Unit := do
  callTests
  creationTests
  destructionTests
  hostWorldTests
  continuationTests

end Tests.RustHullWorld
