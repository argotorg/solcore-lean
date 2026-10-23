import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract

/-! Execute a prepared single-contract scenario. Constructor input is appended
to init code. Successful sends retain storage; read-only test calls discard it.
No source or EVM evaluator is used by this driver. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def lower {α : Type} (result : LowerM α) : IO α :=
  get (result.mapError (fun error => reprStr error))

private def nibble (char : Char) : Except String Nat :=
  if '0' ≤ char && char ≤ '9' then pure (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then pure (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then pure (char.toNat - 'A'.toNat + 10)
  else .error "invalid hexadecimal digit"

private def bytes : List Char → Except String (List UInt8)
  | [] => pure []
  | a :: b :: rest => do return UInt8.ofNat ((← nibble a) * 16 + (← nibble b)) :: (← bytes rest)
  | [_] => .error "incomplete hexadecimal byte"

private def decodeHex (value : String) : Except String (List UInt8) := do
  let '0' :: 'x' :: chars := value.toList | throw "hexadecimal input requires 0x"
  bytes chars

private def hex (value : List UInt8) : String :=
  "0x" ++ String.ofList (value.flatMap fun byte =>
    ["0123456789abcdef".toList[byte.toNat / 16]!, "0123456789abcdef".toList[byte.toNat % 16]!])

private def optionalField (json : Json) (key : String) : Except String (Option Json) := do
  let .obj fields := json | throw "scenario object expected"
  pure ((fields.toList.find? (fun field => field.1 == key)).map Prod.snd)

private def wordField (json : Json) (key : String) : Except String (Option Core.Word) := do
  match ← optionalField json key with
  | none => pure none
  | some value =>
      let text ← value.getStr?
      unless text.length ≤ 78 && !text.isEmpty && text.toList.all Char.isDigit do
        throw s!"{key} must be a decimal word string"
      let some natural := text.toNat? | throw s!"invalid {key}"
      let some word := Core.Word.ofNat? natural | throw s!"{key} exceeds a word"
      if (key = "caller" || key = "address") && natural ≥ 2 ^ 160 then
        throw s!"{key} exceeds an address"
      pure (some word)

private def context (json : Json) : Except String Contract.Context := do
  pure {
    calldata := (← decodeHex (← json.getObjValAs? String "calldata"))
    value := (← wordField json "value").getD Core.Word.zero
    caller := (← wordField json "caller").getD Core.Word.zero
    address := (← wordField json "address").getD Core.Word.zero
    availableGas := (← wordField json "availableGas")
  }

private def fields (result : Contract.Outcome) : List (String × Json) :=
  match result with
  | .returned data storage => [("status", "returned"), ("output", toJson (hex data)),
      ("storage", toJson (storage.map fun (key, value) => [toString key.val, toString value.val]))]
  | .reverted data => [("status", "reverted"), ("output", toJson (hex data))]
  | .invalid => [("status", "invalid")]
  | .outOfFuel _ => [("status", "out-of-fuel")]
  | .languageFailure reason => [("status", "language-failure"), ("detail", toJson (reprStr reason))]
  | .coreFault error => [("status", "core-fault"), ("detail", toJson (reprStr error))]
  | .exportError error => [("status", "export-error"), ("detail", toJson error)]

private def completed : Contract.Outcome → Bool
  | .returned _ _ | .reverted _ | .invalid => true
  | _ => false

private def report (stage : String) (data : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj (("stage", toJson stage) :: data)).compress)

private def execute (config : Json) : IO UInt32 := do
  unless (← get (config.getObjValAs? String "schema")) = "solcore-lean.contract-scenario.v1" do
    throw (IO.userError "unsupported contract scenario schema")
  let hullPath ← get (config.getObjValAs? String "hull")
  let imagePath ← get (config.getObjValAs? String "images")
  let program ← get ((decodeText (← IO.FS.readFile hullPath)).mapError reprStr)
  let images ← get (CodeImage.decode (← IO.FS.readFile imagePath))
  let deployPath ← get (config.getObjValAs? (List String) "deployPath")
  let runtimePath ← get (config.getObjValAs? (List String) "runtimePath")
  let constructor ← get (context (← get (config.getObjVal? "constructor")))
  let prepared ← lower (LinkedContract.prepare program.program deployPath images constructor.calldata
    {constructor with calldata := []})
  let result := Contract.run prepared
  let .returned deployed initialStorage := result | do
    report "deployment" (fields result)
    return if completed result then 0 else 1
  let runtimeImage ← get (CodeImage.select images runtimePath)
  unless deployed == runtimeImage.bytes do
    report "deployment" [("status", "code-mismatch"), ("output", toJson (hex deployed))]
    return 1
  report "deployment" (("codeBytes", toJson deployed.length) :: fields result)
  let calls ← get (config.getObjValAs? (List Json) "calls")
  if calls.isEmpty then return 0
  let compiled ← lower (LinkedContract.compileObject program.program runtimePath images)
  let mut storage := initialStorage
  let mut status := 0
  for (call, index) in calls.zipIdx do
    let context ← get (context call)
    let persist ← match ← get (optionalField call "persist") with
      | none => pure true
      | some value => get value.getBool?
    let result := Contract.run (compiled.instantiate {context with storage})
    report "execution" (("index", toJson index) :: fields result)
    if !completed result then status := 1
    if persist then
      match result with
      | .returned _ nextStorage => storage := nextStorage
      | _ => pure ()
  return status

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: lean --run Tests/RustHullScenarioRun.lean SCENARIO.json"
    return 2
  try execute (← get (Json.parse (← IO.FS.readFile path)))
  catch error =>
    report "preparation" [("status", "rejected"), ("detail", toJson error.toString)]
    return 1
