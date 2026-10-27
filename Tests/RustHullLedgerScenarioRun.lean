import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute a bounded sequence of persistent, zero-value calls from declared
senders on one linked Hull contract with declared observed slots. The keyed
runner requires every call to use the constructor's caller; here the scenario
declares a sender set, the constructor's caller is one of them, and each call
names its own sender as the context's caller. Every row exposes the committed
values of the observed slots and, separately, every nonzero committed slot
outside the declaration, including after a reverted call. Receipt worlds on
failure are not committed snapshots. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull Solcore.Synthesis.Stateful

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
      unless toString natural = text do throw s!"{key} must be a canonical decimal word string"
      let some word := Core.Word.ofNat? natural | throw s!"{key} exceeds a word"
      if (key = "caller" || key = "address") && natural ≥ 2 ^ 160 then
        throw s!"{key} exceeds an address"
      pure (some word)

private def requiredWord (json : Json) (key : String) : Except String Core.Word := do
  let some word ← wordField json key | throw s!"{key} is required"
  pure word

private def context (json : Json) : Except String Contract.Context := do
  let value ← requiredWord json "value"
  unless value == Core.Word.zero do throw "storage scenarios require zero transaction value"
  pure {
    calldata := (← decodeHex (← json.getObjValAs? String "calldata"))
    value := value
    caller := (← requiredWord json "caller")
    address := (← requiredWord json "address")
    availableGas := (← wordField json "availableGas")
    nonce := (← wordField json "nonce").getD (Core.Word.ofNatModulo 1)
  }

private structure Call where
  id : String
  context : Contract.Context

/-- One to eight distinct canonical addresses, none of them the contract. -/
private def senders (config : Json) (constructor : Contract.Context) : Except String (List Core.Word) := do
  let values ← config.getObjValAs? (List Json) "senders"
  unless 1 ≤ values.length && values.length ≤ 8 do throw "senders must contain 1 to 8 addresses"
  let result ← values.foldlM (init := []) fun previous value => do
    let some sender ← wordField (Json.mkObj [("caller", value)]) "caller" | throw "invalid sender"
    if previous.contains sender then throw "duplicate sender"
    if sender == constructor.address then throw "a sender must differ from the contract address"
    pure (previous ++ [sender])
  unless result.contains constructor.caller do throw "the constructor caller must be a declared sender"
  pure result

/-- Validate the whole sequence before deploying or executing any part of it. -/
private def calls (config : Json) (constructor : Contract.Context) (senders : List Core.Word) :
    Except String (List Call) := do
  let values ← config.getObjValAs? (List Json) "calls"
  unless 1 ≤ values.length && values.length ≤ 3 do throw "storage scenarios require 1 to 3 calls"
  values.foldlM (init := []) fun previous value => do
    let id ← value.getObjValAs? String "id"
    unless !id.isEmpty && id.length ≤ 64 && id.toList.all (fun char =>
        ('a' ≤ char && char ≤ 'z') || ('A' ≤ char && char ≤ 'Z') ||
        ('0' ≤ char && char ≤ '9') || char == '_' || char == '-') do
      throw "call ids must contain 1 to 64 ASCII letters, digits, underscores or hyphens"
    if previous.any (fun call => call.id == id) then throw "duplicate call id"
    unless ← value.getObjValAs? Bool "persist" do throw "storage calls must persist"
    let callContext ← context (← value.getObjVal? "context")
    unless callContext.address == constructor.address do
      throw "scenario call address differs from the deployed contract"
    unless senders.contains callContext.caller do
      throw "scenario call caller is not a declared sender"
    pure (previous ++ [⟨id, callContext⟩])

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

private def receiptFields (receipt : Contract.Receipt) : List (String × Json) :=
  ("world", toJson (receipt.world.map fun account => Json.mkObj [
    ("address", toJson (toString account.address.val)),
    ("nonce", toJson (toString account.nonce.val)),
    ("code", account.code.map (fun code => toJson (hex code)) |>.getD Json.null),
    ("storage", toJson (account.storage.map fun (key, value) => [toString key.val, toString value.val])),
    ("transient", toJson (account.transient.map fun (key, value) => [toString key.val, toString value.val])),
    ("created", toJson account.created), ("destroyed", toJson account.destroyed)])) ::
  ("balances", toJson (receipt.balances.map fun (address, value) =>
    [toString address.val, toString value.val])) ::
  ("logs", toJson (receipt.logs.map fun event => Json.mkObj [
    ("address", toJson (toString event.address.val)),
    ("topics", toJson (event.topics.map (fun topic => toString topic.val))),
    ("data", toJson (hex event.data))])) :: fields receipt.outcome

private def committedStorage (slots : List Core.Word) (storage : Core.WordMapping.Entries) : String × Json :=
  ("committedStorage", toJson (slots.map fun slot => Json.mkObj [
    ("slot", toJson (toString slot.val)),
    ("value", toJson (toString (Core.WordMapping.lookupEntries slot storage).val))]))

private def insertNatural (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value < head then value :: head :: tail
      else if value = head then head :: tail
      else head :: insertNatural value tail

/-- Nonzero committed values at slots outside the declaration, in increasing
slot order. A key shadowed by an earlier entry uses the entry lookup selects. -/
private def undeclaredStorage (slots : List Core.Word) (storage : Core.WordMapping.Entries) : String × Json :=
  let keys := (storage.map (·.1.val)).foldl (fun keys key => insertNatural key keys) []
  ("undeclaredStorage", toJson ((keys.filter fun key => !slots.any (·.val == key)).filterMap fun key =>
    let value := Core.WordMapping.lookupEntries (Core.Word.ofNatModulo key) storage
    if value == Core.Word.zero then none
    else some (Json.mkObj [("slot", toJson (toString key)), ("value", toJson (toString value.val))])))

/-- Canonical, strictly increasing decimal Words; at most sixteen. -/
private def observedSlots (config : Json) : Except String (List Core.Word) := do
  let values ← config.getObjValAs? (List Json) "observedSlots"
  unless 1 ≤ values.length && values.length ≤ 16 do throw "observedSlots must contain 1 to 16 slots"
  let slots ← values.mapM fun value => do
    let text ← value.getStr?
    unless text.length ≤ 78 && !text.isEmpty && text.toList.all Char.isDigit do
      throw "observed slots must be decimal word strings"
    let some natural := text.toNat? | throw "invalid observed slot"
    unless toString natural = text do throw "observed slots must be canonical decimal word strings"
    let some word := Core.Word.ofNat? natural | throw "observed slot exceeds a word"
    pure word
  unless (slots.zip (slots.drop 1)).all (fun (left, right) => left.val < right.val) do
    throw "observed slots must be strictly increasing"
  pure slots

/-- The contract's whole committed storage, canonicalized from its entries. -/
private def accountStorage (address : Core.Word) (storage : Core.WordMapping.Entries) : String × Json :=
  ("accountStorage", toJson [AccountStorage.hullAccountJson AccountStorage.contractRole address storage])

private def report (stage : String) (data : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj (("stage", toJson stage) :: data)).compress)

private def execute (config : Json) : IO UInt32 := do
  unless (← get (config.getObjValAs? String "schema")) = "solcore-lean.ledger-contract-scenario.v1" do
    throw (IO.userError "unsupported ledger contract scenario schema")
  let slots ← get (observedSlots config)
  let constructor ← get (context (← get (config.getObjVal? "constructor")))
  unless constructor.caller != constructor.address do
    throw (IO.userError "caller and contract address must differ")
  let senders ← get (senders config constructor)
  let calls ← get (calls config constructor senders)
  let hullPath ← get (config.getObjValAs? String "hull")
  let imagePath ← get (config.getObjValAs? String "images")
  let deployPath ← get (config.getObjValAs? (List String) "deployPath")
  let runtimePath ← get (config.getObjValAs? (List String) "runtimePath")
  let fuel ← match ← get (optionalField config "fuel") with
    | none => pure 10000000
    | some value => do
        let fuel ← get value.getNat?
        unless fuel > 0 && fuel ≤ 1000000000 do throw (IO.userError "fuel must be between 1 and 1000000000")
        pure fuel
  let program ← get ((decodeText (← IO.FS.readFile hullPath)).mapError reprStr)
  let images ← get (CodeImage.decode (← IO.FS.readFile imagePath))
  let runtimeImage ← get (CodeImage.select images runtimePath)
  let prepared ← lower (LinkedContract.prepareDeployment program.program deployPath images constructor.calldata
    {constructor with calldata := [], selfCodeAvailable := false})
  let compiled ← lower (LinkedContract.compileObject program.program runtimePath images)
  let receipt := Contract.runWithReceipt prepared fuel
  let .returned deployed initialStorage := receipt.outcome | do
    report "deployment" (committedStorage slots [] ::
      accountStorage constructor.address [] :: undeclaredStorage slots [] :: receiptFields receipt)
    return 1
  unless deployed == runtimeImage.bytes do
    report "deployment" [committedStorage slots [],
      accountStorage constructor.address [], undeclaredStorage slots [], ("status", "code-mismatch"),
      ("output", toJson (hex deployed))]
    return 1
  report "deployment" (committedStorage slots initialStorage ::
    accountStorage constructor.address initialStorage :: undeclaredStorage slots initialStorage ::
    ("codeBytes", toJson deployed.length) :: receiptFields receipt)
  let mut storage := initialStorage
  let mut balances := receipt.balances
  let mut world := receipt.world
  for (call, index) in calls.zipIdx do
    let context := call.context
    let nonce := (world.find? (·.address == context.address)).map (·.nonce) |>.getD context.nonce
    let receipt := Contract.runWithReceipt (compiled.instantiate {context with
      storage := storage, world := world, nonce := nonce, accounts := balances,
      balance := Core.WordMapping.lookupEntries context.address balances}) fuel
    match receipt.outcome with
    | .returned _ nextStorage =>
        storage := nextStorage
        balances := receipt.balances
        world := receipt.world
    | _ => pure ()
    report "execution" (("index", toJson index) :: ("id", toJson call.id) ::
      committedStorage slots storage ::
        accountStorage constructor.address storage :: undeclaredStorage slots storage :: receiptFields receipt)
    match receipt.outcome with
    | .returned _ _ | .reverted _ => pure ()
    | _ => return 1
  return 0

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: rust-hull-ledger-scenario SCENARIO.json"
    return 2
  try execute (← get (Json.parse (← IO.FS.readFile path)))
  catch error =>
    report "preparation" [("status", "rejected"), ("detail", toJson error.toString)]
    return 1
