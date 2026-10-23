import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract

/-! Execute init code on Core, check returned runtime bytes, then call the
runtime object with storage produced by the constructor. Calls retain storage
only on success. All other call context fields use their documented defaults. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull

private def nibble (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

private def bytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do return UInt8.ofNat ((← nibble a) * 16 + (← nibble b)) :: (← bytes rest)
  | [_] => none

private def decodeHex (value : String) : IO (List UInt8) :=
  match bytes (value.dropPrefix "0x").toString.toList with
  | some bytes => pure bytes
  | none => throw (IO.userError "invalid hexadecimal bytes")

private def hex (value : List UInt8) : String :=
  "0x" ++ String.ofList (value.flatMap fun byte =>
    ["0123456789abcdef".toList[byte.toNat / 16]!, "0123456789abcdef".toList[byte.toNat % 16]!])

private def report (stage status : String) (fields : List (String × Json) := []) : IO Unit :=
  IO.println ((Json.mkObj ([("stage", toJson stage), ("status", toJson status)] ++ fields)).compress)

private def outcome (stage : String) (result : Contract.Outcome) : IO UInt32 := do
  match result with
  | .returned data storage =>
      report stage "returned" [("output", toJson (hex data)),
        ("storage", toJson (storage.map fun (key, value) => [toString key.val, toString value.val]))]
      return 0
  | .reverted data => report stage "reverted" [("output", toJson (hex data))]; return 0
  | .invalid => report stage "invalid"; return 0
  | .outOfFuel _ => report stage "out-of-fuel"; return 1
  | .languageFailure reason => report stage "language-failure" [("detail", toJson (reprStr reason))]; return 1
  | .coreFault error => report stage "core-fault" [("detail", toJson (reprStr error))]; return 1
  | .exportError error => report stage "export-error" [("detail", toJson error)]; return 1

def main (args : List String) : IO UInt32 := do
  let hullPath :: imagePath :: deployPath :: runtimePath :: constructorHex :: valueText :: calls := args | do
    IO.eprintln "usage: lean --run Tests/RustHullDeploymentRun.lean HULL.json IMAGES.json DEPLOY/PATH RUNTIME/PATH CONSTRUCTOR_HEX VALUE [CALLDATA_HEX ...]"
    return 2
  let program ← match decodeText (← IO.FS.readFile hullPath) with
    | .ok value => pure value.program
    | .error error => do report "transport" "rejected" [("detail", toJson (reprStr error))]; return 1
  let images ← match CodeImage.decode (← IO.FS.readFile imagePath) with
    | .ok value => pure value
    | .error error => do report "images" "rejected" [("detail", toJson error)]; return 1
  let some valueNat := valueText.toNat? | do report "input" "rejected" [("detail", "invalid call value")]; return 1
  let some value := Core.Word.ofNat? valueNat | do report "input" "rejected" [("detail", "call value exceeds a word")]; return 1
  let constructorArguments ← decodeHex constructorHex
  let prepared ← match LinkedContract.prepare program (deployPath.splitOn "/") images constructorArguments {value} with
    | .ok value => pure value
    | .error error => do report "deployment-lowering" "rejected" [("detail", toJson (reprStr error))]; return 1
  let result := Contract.run prepared
  let .returned deployed initialStorage := result | outcome "deployment" result
  let expectedImage ← match CodeImage.select images (runtimePath.splitOn "/") with
    | .ok image => pure image
    | .error error => do report "deployment" "rejected" [("detail", toJson error)]; return 1
  unless deployed == expectedImage.bytes do
    report "deployment" "code-mismatch" [("output", toJson (hex deployed))]
    return 1
  report "deployment" "succeeded" [("codeBytes", toJson deployed.length),
    ("storage", toJson (initialStorage.map fun (key, value) => [toString key.val, toString value.val]))]
  if calls.isEmpty then return 0
  let compiled ← match LinkedContract.compileObject program (runtimePath.splitOn "/") images with
    | .ok value => pure value
    | .error error => do report "runtime-lowering" "rejected" [("detail", toJson (reprStr error))]; return 1
  let mut storage := initialStorage
  let mut status := 0
  for data in calls do
    let calldata ← decodeHex data
    let result := Contract.run (compiled.instantiate {storage, calldata})
    if (← outcome "execution" result) != 0 then status := 1
    match result with
    | .returned _ nextStorage => storage := nextStorage
    | _ => pure ()
  return status
