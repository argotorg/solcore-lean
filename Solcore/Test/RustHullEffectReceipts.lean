import Solcore.Frontend.RustHull.Contract

/-! Effects exercised through the public Hull object compiler and Core runner. -/
set_option autoImplicit false
namespace Tests.RustHullEffectReceipts
open Solcore Solcore.Frontend.RustHull

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def name (value : String) : YulName := {name := value}
private def w (value : Nat) : YulExpr := ⟨.literal (.number (toString value)), none⟩
private def call (value : String) (args : List YulExpr := []) : YulExpr := ⟨.call (name value) args, none⟩
private def action (value : String) (args : List YulExpr := []) : YulStmt := ⟨.expression (call value args), none⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def wordBytes (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 256 ^ (31 - index) % 256)
private def source (body : List YulStmt) : Program := {
  functions := []
  entryPoints := []
  objects := [.object "Runtime" {stmts := [⟨.assembly body, none⟩], functions := []} [] none]
}
private def prepare (label : String) (body : List YulStmt) (context : Contract.Context := {}) :
    IO Contract.Prepared :=
  match Contract.prepare (source body) ["Runtime"] context with
  | .ok prepared => pure prepared
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def returned (label : String) (receipt : Contract.Receipt) (expected : List UInt8)
    (logs : List Logs.Event := []) : IO Core.WordMapping.Entries := do
  require (receipt.logs == logs) s!"{label}: incorrect logs {reprStr receipt.logs}"
  match receipt.outcome with
  | .returned actual storage =>
      require (actual == expected) s!"{label}: incorrect output {reprStr actual}"
      pure storage
  | outcome => throw (IO.userError s!"{label}: {reprStr outcome}")
private def slot (entries : Core.WordMapping.Entries) (key value : Nat) : Bool :=
  Core.WordMapping.lookupEntries (word key) entries == word value

private def resumeUntil : Nat → Contract.Receipt → IO Contract.Receipt
  | 0, _ => throw (IO.userError "receipt resumption did not finish")
  | fuel + 1, receipt =>
      match receipt.outcome with
      | .outOfFuel state => do
          require receipt.logs.isEmpty "suspended execution published logs"
          resumeUntil fuel (Contract.resumeWithReceipt state 1000)
      | _ => pure receipt

private def logTests : IO Unit := do
  let input := "abc".toUTF8.toList
  let modified : List UInt8 := [0xee, 0x62, 0x63]
  let context : Contract.Context := {
    calldata := input
    address := word 0xabcd
    caller := word 0x456
    storage := [(word 9, word 5)]
  }
  let body := [action "calldatacopy" [w 0, w 0, w 3], action "log0" [w 0, w 3],
    action "mstore8" [w 0, w 0xee], action "emit", action "sstore" [w 9, w 77],
    action "return" [w 0, w 3], action "log0" [w 0, w 0],
    ⟨.functionDef (name "emit") [] [] [action "log2" [w 0, w 3, w 0x123, call "caller"]], none⟩]
  let prepared ← prepare "ordered logs with a local function" body context
  let logs : List Logs.Event := [
    {address := word 0xabcd, topics := [], data := input},
    {address := word 0xabcd, topics := [word 0x123, word 0x456], data := modified}]
  let storage ← returned "snapshot and local function effects" (Contract.runWithReceipt prepared) modified logs
  require (slot storage 9 77) "successful receipt lost storage writes"
  let suspended := Contract.runWithReceipt prepared 100
  match suspended.outcome with
  | .outOfFuel _ => pure ()
  | other => throw (IO.userError s!"receipt fixture should suspend: {reprStr other}")
  let resumed ← returned "repeated receipt resumption" (← resumeUntil 1000 suspended) modified logs
  require (slot resumed 9 77) "resumed receipt lost storage writes"
  let allTopics := (List.range 5).map fun count =>
    action s!"log{count}" ([w (Core.wordModulus - 1), w 0] ++ (List.range count).map w)
  let prepared ← prepare "log0 through log4" (allTopics ++ [action "stop"]) context
  let expected := (List.range 5).map fun count =>
    {address := word 0xabcd, topics := (List.range count).map word, data := [] : Logs.Event}
  let _ ← returned "all topic counts and empty maximal offset" (Contract.runWithReceipt prepared) [] expected
  let common := [action "mstore8" [w 0, w 0xde], action "log1" [w 0, w 1, w 9],
    action "sstore" [w 9, w 99]]
  for exit in ["revert", "invalid"] do
    let args := if exit == "revert" then [w 0, w 1] else []
    let prepared ← prepare s!"{exit} discards logs" (common ++ [action exit args]) context
    let result := Contract.runWithReceipt prepared
    require result.logs.isEmpty s!"{exit} published logs"
    match exit, result.outcome with
    | "revert", .reverted bytes => require (bytes == [0xde]) "wrong revert payload"
    | "invalid", .invalid => pure ()
    | _, other => throw (IO.userError s!"{exit}: {reprStr other}")
    require (slot prepared.context.storage 9 5) "failed frame changed its input storage"
  let prepared ← prepare "language failure discards logs"
    (common ++ [action "pop" [call "gas"]]) context
  let result := Contract.runWithReceipt prepared
  require result.logs.isEmpty "language failure published logs"
  match result.outcome with
  | .languageFailure (.word reason) => require (reason == word 9) "wrong unavailable gas failure"
  | other => throw (IO.userError s!"missing gas context: {reprStr other}")
  let prepared ← prepare "receipt export limit" [action "calldatacopy" [w 0, w 0, w 3],
    action "log0" [w 0, w 3], action "stop"] context
  let result := Contract.runWithReceipt prepared 1000000 2
  require result.logs.isEmpty "failed receipt export published logs"
  match result.outcome with
  | .exportError _ => pure ()
  | other => throw (IO.userError s!"log export limit was ignored: {reprStr other}")

private def gasTests : IO Unit := do
  let prepared ← prepare "available gas environment input"
    [action "mstore" [w 0, call "gas"], action "mstore" [w 32, call "gas"], action "return" [w 0, w 64]]
    {availableGas := some (word 123456)}
  let _ ← returned "supplied gas stays an explicit environment value" (Contract.runWithReceipt prepared)
    (wordBytes 123456 ++ wordBytes 123456)
  pure ()

private def precompileTests : IO Unit := do
  let input := "abc".toUTF8.toList
  let context : Contract.Context := {calldata := input, address := word 0x42, availableGas := some (word 18)}
  let initial := [action "calldatacopy" [w 0, w 0, w 3],
    action "sstore" [w 0, call "staticcall" [call "gas", w 4, w 0, w 3, w 64, w 2]],
    action "sstore" [w 1, call "returndatasize"]]
  let prepared ← prepare "identity through public effects" (initial ++ [
    action "mstore8" [w 0, w 0xee], action "returndatacopy" [w 96, w 0, w 3],
    action "log1" [w 96, w 3, w 4], action "return" [w 64, w 35]]) context
  let storage ← returned "identity return data snapshot" (Contract.runWithReceipt prepared)
    ([0x61, 0x62] ++ List.replicate 30 0 ++ input)
    [{address := word 0x42, topics := [word 4], data := input}]
  require (slot storage 0 1 && slot storage 1 3) "identity call status or return size is wrong"
  let digest := 0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad
  let prepared ← prepare "SHA256 through public effects" [
    action "calldatacopy" [w 0, w 0, w 3],
    action "sstore" [w 0, call "staticcall" [w 72, w 2, w 0, w 3, w 64, w 7]],
    action "sstore" [w 1, call "returndatasize"], action "log0" [w 64, w 7],
    action "returndatacopy" [w 128, w 0, w 32], action "return" [w 128, w 32]] context
  let storage ← returned "SHA256 retains full return data" (Contract.runWithReceipt prepared)
    (wordBytes digest) [{address := word 0x42, topics := [], data := (wordBytes digest).take 7}]
  require (slot storage 0 1 && slot storage 1 32) "SHA256 call status or return size is wrong"
  for (offset, length, valid) in [(3, 0, true), (4, 0, false), (2, 2, false), (0, 4, false),
      (Core.wordModulus - 1, 1, false)] do
    let prepared ← prepare "return data bounds" (initial ++ [action "log0" [w 0, w 0],
      action "returndatacopy" [w (if length == 0 then Core.wordModulus - 1 else 128), w offset, w length],
      action "stop"]) context
    let result := Contract.runWithReceipt prepared
    if valid then
      let _ ← returned "empty copy exactly at return-data end" result []
        [{address := word 0x42, topics := [], data := []}]
      pure ()
    else
      require result.logs.isEmpty "out-of-bounds return data copy published logs"
      match result.outcome with
      | .invalid => pure ()
      | other => throw (IO.userError s!"return data bounds {offset} {length}: {reprStr other}")
  let prepared ← prepare "initial return data is empty"
    [action "returndatacopy" [w 0, w 1, w 0], action "stop"]
  match (Contract.runWithReceipt prepared).outcome with
  | .invalid => pure ()
  | other => throw (IO.userError s!"initial return-data bounds: {reprStr other}")

def run : IO Unit := do
  logTests
  gasTests
  precompileTests

end Tests.RustHullEffectReceipts
