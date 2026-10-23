import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.Contract
import Solcore.Abi.Keccak256

/-! Execute actual checked Rust std.opcodes call sites through imported Hull. -/
set_option autoImplicit false
open Solcore Solcore.Core Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def word (value : Nat) : Word := Word.ofNatModulo value
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (Word.byteAt (word index) (word value)).val
private def digest (bytes : List UInt8) : List UInt8 :=
  (Solcore.Abi.V1.Keccak256.hash bytes.toByteArray).toList
private def number (bytes : List UInt8) : Nat := bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0
private def context : Contract.Context := {
  address := word 0xaaa, caller := word 0xbbb, balance := word 100,
  value := word 17, nonce := word 1, availableGas := some (word 100000), completeWorld := true}
private def ambient : Ambient.Context := {
  origin := some (word (2 ^ 200 + 0x111)), gasprice := some (word 2),
  coinbase := some (word (2 ^ 200 + 0x222)), timestamp := some (word 3),
  number := some (word 300), prevrandao := some (word 4), gaslimit := some (word 5),
  chainid := some (word 6), basefee := some (word 7), blobbasefee := some (word 8),
  blockHashes := some [(word 44, word 9)], blobHashes := some [word 10]}
private def compile (program : Solcore.Frontend.RustHull.Program) (name : String) : IO Contract.CompiledObject :=
  match Contract.compileObject program [name ++ "Deploy", name] with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"{name}: {reprStr error}")
private def returned (name : String) (compiled : Contract.CompiledObject) (context : Contract.Context)
    (bytes : List UInt8) : IO Contract.Receipt := do
  let receipt := Contract.runWithReceipt (compiled.instantiate context) 10000000
  match receipt.outcome with
  | .returned actual _ => require (actual == bytes) s!"{name}: wrong output"
  | other => throw (IO.userError s!"{name}: {reprStr other}")
  pure receipt
private def invalid (name : String) (compiled : Contract.CompiledObject) : IO Unit := do
  let receipt := Contract.runWithReceipt (compiled.instantiate {context with isStatic := true})
  match receipt.outcome with
  | .invalid => do
      require (receipt.world.isEmpty && receipt.balances.isEmpty && receipt.logs.isEmpty)
        s!"{name}: invalid transaction exported state"
  | other => throw (IO.userError s!"{name}: static execution unexpectedly completed: {reprStr other}")

def main (arguments : List String) : IO Unit := do
  let [file] := arguments | throw (IO.userError "expected one checked Hull export")
  let envelope ← match decodeText (← IO.FS.readFile file) with
    | .ok result => pure result
    | .error error => throw (IO.userError (reprStr error))
  let readings ← compile envelope.program "AmbientWrappers"
  discard (returned "twelve ambient std wrappers" readings {context with ambient}
    ([0x111, 2, 0x222, 3, 300, 4, 5, 6, 7, 8, 9, 10].flatMap wordBytes))
  match Contract.run (readings.instantiate context) with
  | .languageFailure (.word reason) => require (reason == word 14) "missing ambient context changed reason"
  | other => throw (IO.userError s!"missing ambient context was accepted: {reprStr other}")
  let inspection ← compile envelope.program "InspectionWrappers"
  let targetCode : List UInt8 := [0x61, 0x62, 0x63]
  discard (returned "three inspection std wrappers" inspection
    {context with world := [{address := word 0xccc, nonce := word 1, code := some targetCode}]}
    (wordBytes 3 ++ digest targetCode ++ targetCode ++ List.replicate 29 0))
  let calls ← compile envelope.program "CallModeWrappers"
  discard (returned "callcode and delegatecall std wrappers" calls context (wordBytes 1 ++ wordBytes 1))
  discard (returned "static callcode and delegatecall std wrappers" calls
    {context with isStatic := true} (wordBytes 1 ++ wordBytes 1))
  let creation ← compile envelope.program "CreationWrappers"
  let creator := (wordBytes 0xaaa).drop 12
  let created := number ((digest ([0xd6, 0x94] ++ creator ++ [1])).drop 12)
  let salted := number ((digest ([0xff] ++ creator ++ wordBytes 77 ++ digest [])).drop 12)
  let receipt ← returned "create and create2 std wrappers" creation context
    (wordBytes created ++ wordBytes salted)
  let account address := receipt.world.find? (·.address == word address)
  require ((account 0xaaa).map (·.nonce) == some (word 3)) "CREATE wrappers did not advance creator nonce"
  for address in [created, salted] do
    match account address with
    | some record => require (record.nonce == word 1 && record.code == some [] &&
        !record.created && !record.destroyed) "created wrapper account not finalized correctly"
    | none => throw (IO.userError "missing created wrapper account")
  invalid "static creation wrappers" creation
  let destruction ← compile envelope.program "DestructionWrapper"
  let receipt ← returned "selfdestruct std wrapper" destruction
    {context with accounts := [(word 0xdef, word 3)], storage := [(word 7, word 9)]} []
  require (WordMapping.lookupEntries (word 0xaaa) receipt.balances == Word.zero &&
    WordMapping.lookupEntries (word 0xdef) receipt.balances == word 103)
    "selfdestruct wrapper did not transfer balance"
  require ((receipt.world.find? (·.address == word 0xaaa)).map (·.storage) == some [(word 7, word 9)])
    "selfdestruct wrapper removed an existing account"
  let receipt ← returned "created selfdestruct std wrapper" destruction
    {context with created := true} []
  require (!(receipt.world.any (·.address == word 0xaaa))) "created selfdestruct account survived finalization"
  invalid "static selfdestruct wrapper" destruction
  IO.println "20 new std.opcodes wrappers executed through checked Rust source, Hull and Core"
