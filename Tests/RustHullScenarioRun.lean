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

private def accounts (config : Json) : Except String (Core.WordMapping.Entries × List Core.Word) := do
  let some value ← optionalField config "accounts" | pure ([], [])
  let values ← value.getArr?
  values.toList.foldlM (init := ([], [])) fun (balances, empty) value => do
    let some address ← wordField value "address" | throw "account address required"
    let balance := (← wordField value "balance").getD Core.Word.zero
    if balances.any (fun entry => entry.1 == address) then throw "duplicate account address"
    let isEmpty ← match ← optionalField value "empty" with
      | none => pure false
      | some flag => flag.getBool?
    pure (balances ++ [(address, balance)], if isEmpty then address :: empty else empty)

/-- Top-level transaction preparation. Failed transactions and non-persistent
test calls discard the prepared ledger together with their execution receipt. -/
private def transfer (balances : Core.WordMapping.Entries) (context : Contract.Context) :
    Except String Core.WordMapping.Entries := do
  let source := Core.WordMapping.lookupEntries context.caller balances
  let target := Core.WordMapping.lookupEntries context.address balances
  if source.val < context.value.val then throw "transaction sender has insufficient balance"
  if context.caller == context.address then return balances
  let some credited := Core.Word.ofNat? (target.val + context.value.val) |
    throw "transaction balance overflow"
  return Core.WordMapping.insertEntries context.address credited
    (Core.WordMapping.insertEntries context.caller
      (Core.Word.ofNatModulo (source.val - context.value.val)) balances)

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

private def receiptFields (receipt : Contract.Receipt) : List (String × Json) :=
  ("balances", toJson (receipt.balances.map fun (address, value) =>
    [toString address.val, toString value.val])) ::
  ("logs", toJson (receipt.logs.map fun event => Json.mkObj [
    ("address", toJson (toString event.address.val)),
    ("topics", toJson (event.topics.map (fun topic => toString topic.val))),
    ("data", toJson (hex event.data))])) :: fields receipt.outcome

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
  let (initialBalances, emptyAccounts) ← get (accounts config)
  let fuel ← match ← get (optionalField config "fuel") with
    | none => pure 10000000
    | some value => do
        let fuel ← get value.getNat?
        unless fuel > 0 && fuel ≤ 1000000000 do throw (IO.userError "fuel must be between 1 and 1000000000")
        pure fuel
  let constructor ← get (context (← get (config.getObjVal? "constructor")))
  let entryBalances ← get (transfer initialBalances constructor)
  let prepared ← lower (LinkedContract.prepareDeployment program.program deployPath images constructor.calldata
    {constructor with
      calldata := [], selfCodeAvailable := false, accounts := entryBalances, emptyAccounts := emptyAccounts,
      balance := Core.WordMapping.lookupEntries constructor.address entryBalances})
  let receipt := Contract.runWithReceipt prepared fuel
  let result := receipt.outcome
  let .returned deployed initialStorage := result | do
    report "deployment" (receiptFields receipt)
    return if completed result then 0 else 1
  let runtimeImage ← get (CodeImage.select images runtimePath)
  unless deployed == runtimeImage.bytes do
    report "deployment" [("status", "code-mismatch"), ("output", toJson (hex deployed))]
    return 1
  report "deployment" (("codeBytes", toJson deployed.length) :: receiptFields receipt)
  let calls ← get (config.getObjValAs? (List Json) "calls")
  if calls.isEmpty then return 0
  let compiled ← lower (LinkedContract.compileObject program.program runtimePath images)
  let mut storage := initialStorage
  let mut balances := receipt.balances
  let mut status := 0
  for (call, index) in calls.zipIdx do
    let context ← get (context call)
    unless context.address == constructor.address do
      throw (IO.userError "scenario call address differs from the deployed contract")
    let persist ← match ← get (optionalField call "persist") with
      | none => pure true
      | some value => get value.getBool?
    let entryBalances ← get (transfer balances context)
    let receipt := Contract.runWithReceipt (compiled.instantiate {context with
      storage := storage,
      accounts := entryBalances, emptyAccounts := emptyAccounts,
      balance := Core.WordMapping.lookupEntries context.address entryBalances}) fuel
    let result := receipt.outcome
    report "execution" (("index", toJson index) :: receiptFields receipt)
    if !completed result then status := 1
    if persist then
      match result with
      | .returned _ nextStorage =>
          storage := nextStorage
          balances := receipt.balances
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
