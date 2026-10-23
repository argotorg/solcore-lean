import Solcore.Frontend.RustHull.Contract

/-! Public contract execution tests for linked constructor and runtime objects.
The byte images below were produced by solc 0.8.35, optimized Yul, Osaka. They
describe the same constructor and runtime operations as the checked Hull trees.
Address and code-hash constants were independently checked with Foundry cast. -/
set_option autoImplicit false
namespace Tests.RustHullCreationAccounts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def ident (value : String) : YulExpr := ⟨.ident (name value), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr :=
  ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt :=
  ⟨.expression (call value args), none⟩
private def binding (value : String) (init : YulExpr) : YulStmt :=
  ⟨.letDecl [name value] (some init), none⟩
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def words (values : List Nat) : List UInt8 := values.flatMap wordBytes
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Object" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}

private def runtimeBytes : List UInt8 :=
  [0x36, 0x60, 0x0c, 0x57, 0x5f, 0x54, 0x5f, 0x52, 0x60, 0x20, 0x5f, 0xf3, 0x5b, 0x33, 0xff]
private def initBytes : List UInt8 :=
  [0x60, 0x2a, 0x5f, 0x55, 0x60, 0x0f, 0x80, 0x60, 0x0e, 0x5f, 0x39, 0x5f, 0xf3, 0xfe] ++ runtimeBytes
private def argsInitBytes : List UInt8 :=
  [0x60, 0x20, 0x60, 0x23, 0x5f, 0x39, 0x5f, 0x51, 0x5f, 0x55,
    0x60, 0x0f, 0x80, 0x60, 0x14, 0x5f, 0x39, 0x5f, 0xf3, 0xfe] ++ runtimeBytes
private def revertInitBytes : List UInt8 :=
  [0x61, 0xde, 0xad, 0x5f, 0x52, 0x60, 0x02, 0x60, 0x1e, 0xfd]
private def bytesNat (bytes : List UInt8) : Nat :=
  bytes.foldl (fun accum byte => accum * 256 + byte.toNat) 0
private def writeBytes (bytes : List UInt8) : List YulStmt :=
  ((List.range ((bytes.length + 31) / 32)).map fun index =>
    let chunk := (bytes.drop (32 * index)).take 32
    action "mstore" [w (32 * index), w (bytesNat chunk * 256 ^ (32 - chunk.length))])
private def runtimeBody : List YulStmt :=
  [⟨.ifThen (call "calldatasize") [action "selfdestruct" [call "caller"]], none⟩,
    action "mstore" [w 0, call "sload" [w 0]], action "return" [w 0, w 32]]
private def installBody : List YulStmt :=
  writeBytes runtimeBytes ++ [action "return" [w 0, w runtimeBytes.length]]
private def initBody : List YulStmt := [action "sstore" [w 0, w 42]] ++ installBody
private def argsInitBody : List YulStmt :=
  [action "codecopy" [w 0, w argsInitBytes.length, w 32],
    action "sstore" [w 0, call "mload" [w 0]]] ++ installBody
private def revertInitBody : List YulStmt :=
  [action "sstore" [w 0, w 99], action "mstore" [w 0, w 0xdead], action "revert" [w 30, w 2]]
private def definition (body : List YulStmt) (bytes : List UInt8) (isInit := false) :
    AccountRuntime.CodeDefinition :=
  {program := source body, path := ["Object"], bytes := bytes, isInit := isInit}
private def catalog : List AccountRuntime.CodeDefinition :=
  [definition initBody initBytes true, definition runtimeBody runtimeBytes,
    definition argsInitBody argsInitBytes true, definition revertInitBody revertInitBytes true]

private def createAddress : Nat := 0x21e44f0740e8cf48922d40250130b7fa7d305f15
private def nextAddress : Nat := 0x70e557a98d22b20fd7da0ba75118691f181defe4
private def create2Address : Nat := 0xd214e0541c6aba1cc87085b4616d8a220ad1da27
private def runtimeHash : Nat := 0xeeedf27530da124ff00108ae56d27fd186832aec5173f01879721fec8410307d
private def context : Contract.Context := {
  address := word 0xaaaa
  caller := word 0xbbbb
  nonce := word 7
  balance := word 100
  availableGas := some (word 10000000)
  completeWorld := true
}
private def create (value := 17) : YulExpr := call "create" [w value, w 0, w initBytes.length]
private def create2 : YulExpr := call "create2" [w 17, w 0, w initBytes.length, w 7]
private def childCall (inputLength := 0) : YulExpr :=
  call "call" [w 1000000, ident "child", w 0, w 0, w inputLength, w 64, w 32]
private def output (values : List YulExpr) : List YulStmt :=
  (values.zipIdx).map (fun (value, index) => action "mstore" [w (128 + 32 * index), value]) ++
    [action "return" [w 128, w (32 * values.length)]]

private def successBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create, binding "status" childCall,
    action "extcodecopy" [ident "child", w 352, w 3, w 20]] ++
  ((output [ident "child", ident "status", call "mload" [w 64],
    call "extcodesize" [ident "child"], call "balance" [ident "child"],
    call "returndatasize", call "extcodehash" [ident "child"]]).dropLast) ++
  [action "return" [w 128, w 244]]
private def repeatedBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create2, binding "second" create2] ++
  output [ident "child", ident "second", call "extcodesize" [ident "child"]]
private def revertBody : List YulStmt :=
  writeBytes revertInitBytes ++
  [binding "failed" (call "create" [w 17, w 0, w revertInitBytes.length]),
    binding "returnSize" (call "returndatasize"), action "returndatacopy" [w 64, w 0, w 2]] ++
  writeBytes initBytes ++ [binding "child" create] ++
  output [ident "failed", ident "returnSize", call "mload" [w 64], ident "child"]
private def destructionBody : List YulStmt :=
  writeBytes initBytes ++ [binding "child" create2, binding "status" (childCall 1),
    binding "sizeBeforeEnd" (call "extcodesize" [ident "child"]), binding "second" create2] ++
  output [ident "child", ident "status", ident "sizeBeforeEnd", ident "second",
    call "balance" [ident "child"], call "selfbalance"]
private def argsBody : List YulStmt :=
  writeBytes (argsInitBytes ++ wordBytes 77) ++
  [binding "child" (call "create" [w 17, w 0, w (argsInitBytes.length + 32)]),
    binding "status" childCall] ++
  output [ident "child", ident "status", call "mload" [w 64]]
private def parentBody : List YulStmt :=
  [⟨.switch (call "calldataload" [w 0])
    ([(0, successBody), (1, repeatedBody), (2, revertBody),
      (3, writeBytes initBytes ++ [action "pop" [create], action "revert" [w 0, w 0]]),
      (4, destructionBody), (5, argsBody),
      (6, [action "mstore8" [w 0, w 0xff], action "pop" [call "create" [w 0, w 0, w 1]]])].map
      fun (value, body) => ⟨.number (toString value), body, none⟩)
    (some [action "invalid"]), none⟩]

private def compile (entries := catalog) : IO Contract.CompiledObject :=
  match Contract.compileObject (source parentBody) ["Object"] 4096 none entries with
  | .ok compiled => pure compiled
  | .error error => throw (IO.userError s!"creation accounts compile: {reprStr error}")
private def execute (compiled : Contract.CompiledObject) (selector : Nat)
    (supplied := context) (fuel := 10000000) : Contract.Receipt :=
  Contract.runWithReceipt (compiled.instantiate {supplied with calldata := wordBytes selector}) fuel
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8) : IO Unit := do
  require receipt.logs.isEmpty s!"{label}: unexpected logs"
  match receipt.outcome with
  | .returned actual _ => require (actual == expected) s!"{label}: unexpected bytes {reprStr actual}"
  | other => throw (IO.userError s!"{label}: {reprStr other}")
private def account (label : String) (receipt : Contract.Receipt) (address : Nat) : IO AccountState.Account :=
  match receipt.world.find? (·.address == word address) with
  | some result => pure result
  | none => throw (IO.userError s!"{label}: missing account {address}")
private def balance (label : String) (receipt : Contract.Receipt) (address expected : Nat) : IO Unit :=
  require (Core.WordMapping.lookupEntries (word address) receipt.balances == word expected)
    s!"{label}: incorrect balance at {address}"
private def nonce (label : String) (receipt : Contract.Receipt) (address expected : Nat) : IO Unit := do
  let actual ← account label receipt address
  require (actual.nonce == word expected) s!"{label}: incorrect nonce"
private def childState (label : String) (receipt : Contract.Receipt) (address stored : Nat) : IO Unit := do
  let actual ← account label receipt address
  require (actual.code == some runtimeBytes && actual.nonce == word 1)
    s!"{label}: wrong installed code or nonce"
  require (Core.WordMapping.lookupEntries (word 0) actual.storage == word stored)
    s!"{label}: constructor storage lost"
  require (actual.transient.isEmpty && !actual.created && !actual.destroyed)
    s!"{label}: transaction finalization did not clear flags/transient"
private def noPublishedState (label : String) (receipt : Contract.Receipt) : IO Unit :=
  require (receipt.world.isEmpty && receipt.balances.isEmpty && receipt.logs.isEmpty)
    s!"{label}: failed/suspended execution published state"
private def resumeCreation : Nat → Contract.Receipt → IO (Contract.Receipt × Nat)
  | 0, _ => throw (IO.userError "creation checkpoint budget exhausted")
  | remaining + 1, receipt => match receipt.outcome with
      | .outOfFuel state => do
          noPublishedState "creation checkpoint" receipt
          let (result, count) ← resumeCreation remaining (Contract.resumeWithReceipt state 5000)
          pure (result, count + 1)
      | _ => pure (receipt, 0)

def run : IO Unit := do
  let compiled ← compile
  let supplied := {context with accounts := [(word createAddress, word 5)]}
  let expected := words [createAddress, 1, 42, 15, 22, 32, runtimeHash] ++
    runtimeBytes.drop 3 ++ List.replicate 8 0
  let success := execute compiled 0 supplied
  returned "CREATE, CALL and exact child code inspection" success expected
  childState "created runtime" success createAddress 42
  nonce "creator increment" success 0xaaaa 8
  balance "creator debit" success 0xaaaa 83
  balance "prefunded child" success createAddress 22

  let suspended := execute compiled 0 supplied 1000
  noPublishedState "creation checkpoint" suspended
  let (resumed, checkpoints) ← resumeCreation 3000 suspended
  require (checkpoints > 1) "creation did not cross repeated checkpoints"
  returned "creation resume" resumed expected
  childState "creation resume storage/code" resumed createAddress 42
  nonce "creation resume increments once" resumed 0xaaaa 8
  require (success.balances == resumed.balances) "creation resume changed balances"

  let repeated := execute compiled 1
  returned "CREATE2 address and repeated collision" repeated (words [create2Address, 0, 15])
  childState "CREATE2 retained runtime" repeated create2Address 42
  nonce "CREATE2 collision retains second nonce increment" repeated 0xaaaa 9
  balance "CREATE2 collision refunds value" repeated 0xaaaa 83

  let reverted := execute compiled 2
  returned "constructor revert bytes and next CREATE nonce" reverted
    (words [0, 2, 0xdead * 256 ^ 30, nextAddress])
  require (!(reverted.world.any (·.address == word createAddress))) "reverted constructor left an account"
  childState "CREATE after reverted constructor" reverted nextAddress 42
  nonce "reverted constructor nonce remains consumed" reverted 0xaaaa 9
  balance "reverted constructor value refunded" reverted 0xaaaa 83

  let collision := execute compiled 0 {context with world := [{address := word createAddress, nonce := word 1}]}
  -- CREATE returns zero on collision. Subsequent empty-account CALL succeeds and
  -- all zero-address observations remain empty; its EXTCODEHASH is zero.
  returned "preexisting nonce collision" collision (words [0, 1, 0, 0, 0, 0, 0] ++ List.replicate 20 0)
  nonce "collision increments creator" collision 0xaaaa 8
  nonce "collision keeps target" collision createAddress 1
  balance "collision retains sender value" collision 0xaaaa 100

  let destroyed := execute compiled 4
  returned "SELFDESTRUCT keeps code until transaction end and CREATE2 still collides" destroyed
    (words [create2Address, 1, 15, 0, 0, 100])
  require (!(destroyed.world.any (·.address == word create2Address))) "created-and-destroyed account survived finalization"
  balance "destroyed target balance cleared" destroyed create2Address 0
  balance "SELFDESTRUCT beneficiary credited" destroyed 0xaaaa 100
  nonce "pending deletion blocks recreation" destroyed 0xaaaa 9

  let args := execute compiled 5
  returned "constructor reads suffix through CODECOPY" args (words [createAddress, 1, 77])
  childState "constructor suffix storage" args createAddress 77

  let parentRevert := execute compiled 3
  noPublishedState "parent revert discards created child" parentRevert
  match parentRevert.outcome with
  | .reverted [] => pure ()
  | other => throw (IO.userError s!"parent revert after creation: {reprStr other}")
  let static := execute compiled 0 {context with isStatic := true}
  noPublishedState "static CREATE" static
  match static.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"static CREATE: {reprStr other}")
  let static2 := execute compiled 1 {context with isStatic := true}
  noPublishedState "static CREATE2" static2
  match static2.outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"static CREATE2: {reprStr other}")
  let unknown := execute compiled 6
  noPublishedState "unknown init bytes" unknown
  match unknown.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "unknown init has incorrect failure"
  | other => throw (IO.userError s!"unknown init: {reprStr other}")
  let ambiguous ← compile (definition initBody (initBytes.take 4) true :: catalog)
  let ambiguous := execute ambiguous 0
  noPublishedState "ambiguous init prefix" ambiguous
  match ambiguous.outcome with
  | .languageFailure (.word reason) => require (reason == word 16) "ambiguous init has incorrect failure"
  | other => throw (IO.userError s!"ambiguous init prefix: {reprStr other}")
  IO.println "Rust Hull creation account tests passed"

end Tests.RustHullCreationAccounts
