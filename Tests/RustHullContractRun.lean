import Lean.Data.Json
import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.Contract

/-! Run one exported Hull runtime object with exact byte calldata on Core. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull

private def hexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | first :: second :: rest => do
      return UInt8.ofNat ((← hexDigit first) * 16 + (← hexDigit second)) :: (← hexBytes rest)
  | [_] => none

private def encodeHex (bytes : List UInt8) : String :=
  "0x" ++ String.ofList (bytes.flatMap fun byte =>
    ["0123456789abcdef".toList[byte.toNat / 16]!, "0123456789abcdef".toList[byte.toNat % 16]!])

private def report (stage status : String) (fields : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj ([("stage", toJson stage), ("status", toJson status)] ++ fields)).compress)

private def runCall (compiled : Contract.CompiledObject) (data : String)
    (availableGas : Option Core.Word) : IO UInt32 := do
  let calldata ← match hexBytes (data.dropPrefix "0x").toString.toList with
    | some bytes => pure bytes
    | none => do report "input" "rejected" [("detail", "invalid calldata hex")]; return 1
  match Contract.run (compiled.instantiate {calldata, availableGas}) with
  | .returned bytes storage =>
      report "execution" "returned" [("output", toJson (encodeHex bytes)),
        ("storage", toJson (storage.map fun (key, value) => [toString key.val, toString value.val]))]
      return 0
  | .reverted bytes => report "execution" "reverted" [("output", toJson (encodeHex bytes))]; return 0
  | .invalid => report "execution" "invalid" []; return 0
  | .outOfFuel _ => report "execution" "out-of-fuel" []; return 1
  | .languageFailure reason => report "execution" "language-failure" [("detail", toJson (reprStr reason))]; return 1
  | .coreFault error => report "execution" "core-fault" [("detail", toJson (reprStr error))]; return 1
  | .exportError error => report "execution" "export-error" [("detail", toJson error)]; return 1

def main (args : List String) : IO UInt32 := do
  let (availableGas, args) ← match args with
    | "--gas" :: text :: rest =>
        match text.toNat? >>= Core.Word.ofNat? with
        | some word => pure (some word, rest)
        | none => do report "input" "rejected" [("detail", "invalid explicit gas input")]; return 1
    | _ => pure (none, args)
  let (path, object, inputs) ← match args with
    | [path, object, data] => pure (path, object, [data])
    | [path, object, "--batch", inputPath] =>
        match Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := List String) with
        | .ok inputs => pure (path, object, inputs)
        | .error error => do report "input" "rejected" [("detail", toJson error)]; return 1
    | _ => do
        IO.eprintln "usage: lean --run Tests/RustHullContractRun.lean EXPORT.json OBJECT/PATH CALLDATA_HEX | --batch INPUTS.json"
        return 2
  let envelope ← match decodeText (← IO.FS.readFile path) with
    | .ok value => pure value
    | .error error => do report "transport" "rejected" [("detail", toJson (reprStr error))]; return 1
  let compiled ← match Contract.compileObject envelope.program (object.splitOn "/") with
    | .ok value => pure value
    | .error error => do report "lowering" "rejected" [("detail", toJson (reprStr error))]; return 1
  let mut status := 0
  for data in inputs do
    if (← runCall compiled data availableGas) != 0 then status := 1
  return status
