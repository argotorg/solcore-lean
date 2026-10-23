import Lean.Data.Json
import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.Contract

/-! Count actual Core transitions for one runtime call, with an explicit cap. -/
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

private def profile : Nat → Nat → Core.State → Nat × Core.State
  | remaining, used, state =>
      match Core.advance state with
      | .done _ | .fault _ => (used, state)
      | .next next => match remaining with
        | 0 => (used, state)
        | fuel + 1 => profile fuel (used + 1) next

def main (args : List String) : IO UInt32 := do
  let [path, object, data, limit] := args | do
    IO.eprintln "usage: lean --run Tests/RustHullContractProfile.lean EXPORT OBJECT CALLDATA_HEX MAX_STEPS"
    return 2
  let some fuel := limit.toNat? | do IO.eprintln "invalid step limit"; return 2
  let some calldata := hexBytes (data.dropPrefix "0x").toString.toList | do
    IO.eprintln "invalid calldata hex"; return 2
  let .ok envelope := decodeText (← IO.FS.readFile path) | do IO.eprintln "invalid Hull export"; return 1
  let prepared ← match Contract.prepare envelope.program (object.splitOn "/") {calldata} with
    | .ok result => pure result
    | .error error => do IO.eprintln (reprStr error); return 1
  let (steps, state) := profile fuel 0 (.initial prepared.expression)
  let (status, fields) := match Contract.resume state 0 with
    | .returned bytes _ => ("returned", [("output", toJson (encodeHex bytes))])
    | .reverted bytes => ("reverted", [("output", toJson (encodeHex bytes))])
    | .invalid => ("invalid", [])
    | .outOfFuel _ => ("out-of-fuel", [])
    | .languageFailure reason => ("language-failure", [("detail", toJson (reprStr reason))])
    | .coreFault error => ("core-fault", [("detail", toJson (reprStr error))])
    | .exportError error => ("export-error", [("detail", toJson error)])
  IO.println (Json.mkObj ([("status", toJson status), ("steps", toJson steps),
    ("limit", toJson fuel), ("scope", toJson "runtimeOnly")] ++ fields)).compress
  return if status == "returned" || status == "reverted" then 0 else 1
