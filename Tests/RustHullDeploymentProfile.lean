import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract

/-! Count Core transitions for a constructor with no ABI arguments. This driver
uses the pinned raw-scenario sender and CREATE address, explicit gas input,
and an explicit transition cap. It does not change the runtime's default fuel. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull

private def profile : Nat → Nat → Core.State → Nat × Core.State
  | remaining, used, state =>
      match Core.advance state with
      | .done _ | .fault _ => (used, state)
      | .next next => match remaining with
        | 0 => (used, state)
        | fuel + 1 => profile fuel (used + 1) next

def main (args : List String) : IO UInt32 := do
  let [path, imagePath, object, runtime, limit, gasText] := args | do
    IO.eprintln "usage: lean --run Tests/RustHullDeploymentProfile.lean HULL IMAGES DEPLOY_PATH RUNTIME_PATH MAX_STEPS AVAILABLE_GAS"
    return 2
  let some fuel := limit.toNat? | do IO.eprintln "invalid step limit"; return 2
  let some gas := gasText.toNat? | do IO.eprintln "invalid gas input"; return 2
  let some gas := Core.Word.ofNat? gas | do IO.eprintln "gas exceeds a word"; return 2
  let .ok envelope := decodeText (← IO.FS.readFile path) | do IO.eprintln "invalid Hull"; return 1
  let .ok images := CodeImage.decode (← IO.FS.readFile imagePath) | do IO.eprintln "invalid images"; return 1
  let .ok expected := CodeImage.select images (runtime.splitOn "/") | do IO.eprintln "missing runtime image"; return 1
  let caller := Core.Word.ofNatModulo 0x1212121212121212121212121212120000000012
  let address := Core.Word.ofNatModulo 0x822d76f4c4ac0d26e89071fb06f116e7f3fc7a56
  let balances := Core.WordMapping.insertEntries address Core.Word.zero
    [(caller, Core.Word.ofNatModulo 0x10000000000000000000000000)]
  let prepared ← match LinkedContract.prepareDeployment envelope.program (object.splitOn "/") images [] {
      caller := caller, address := address, accounts := balances, emptyAccounts := [caller]
      availableGas := some gas } with
    | .ok result => pure result
    | .error error => do IO.eprintln (reprStr error); return 1
  let (steps, state) := profile fuel 0 (.initial prepared.expression)
  let (status, fields) := match Contract.resume state 0 with
    | .returned bytes storage =>
        (if bytes == expected.bytes then "returned" else "code-mismatch",
          [("codeBytes", toJson bytes.length), ("storageEntries", toJson storage.length)])
    | .reverted _ => ("reverted", [])
    | .invalid => ("invalid", [])
    | .outOfFuel _ => ("out-of-fuel", [])
    | .languageFailure reason => ("language-failure", [("detail", toJson (reprStr reason))])
    | .coreFault error => ("core-fault", [("detail", toJson (reprStr error))])
    | .exportError error => ("export-error", [("detail", toJson error)])
  IO.println (Json.mkObj ([("status", toJson status), ("steps", toJson steps),
    ("limit", toJson fuel), ("availableGas", toJson gasText),
    ("scope", toJson "raw-empty-argument-constructor"),
    ("initialAccounts", toJson (balances.map fun (key, value) => [toString key.val, toString value.val])),
    ("selfCodeAvailable", toJson false), ("evmGasMetering", toJson false)] ++ fields)).compress
  return if status == "returned" then 0 else 1
