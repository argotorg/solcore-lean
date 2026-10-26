import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract

/-! Execute a bounded sequence of persistent, value-bearing calls on one linked
Hull contract with declared observed slots. As for ordinary Hull top-level
execution, the runner performs each checked value transfer in its ledger and
supplies the resulting entry balance and ledger; constructor execution observes
its deployment value the same way. Every row exposes the committed values of
the declared slots, every nonzero committed slot outside them and the
contract's committed balance. A failed call commits neither its transfer nor
its receipt world; a rejected transfer is reported, never executed. -/
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

/-- Validate the whole sequence before deploying or executing any part of it. -/
private def calls (config : Json) (constructor : Contract.Context) : Except String (List Call) := do
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
    unless callContext.caller == constructor.caller do
      throw "scenario call caller differs from the constructor caller"
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

private def report (stage : String) (data : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj (("stage", toJson stage) :: data)).compress)

/-- Debit the sender and credit the recipient with checked arithmetic, exactly
once per message; a zero value leaves the ledger unchanged. -/
private def transfer (balances : Core.WordMapping.Entries) (source target amount : Core.Word) :
    Except String Core.WordMapping.Entries := do
  if amount == Core.Word.zero then return balances
  let before := Core.WordMapping.lookupEntries source balances
  let recipient := Core.WordMapping.lookupEntries target balances
  unless amount.val ≤ before.val do throw "insufficient sender balance"
  let some credited := Core.Word.ofNat? (recipient.val + amount.val) | throw "recipient balance overflow"
  pure (Core.WordMapping.insertEntries target credited
    (Core.WordMapping.insertEntries source (Core.Word.ofNatModulo (before.val - amount.val)) balances))

private def committedBalance (address : Core.Word) (balances : Core.WordMapping.Entries) : String × Json :=
  ("committedBalance", toJson (toString (Core.WordMapping.lookupEntries address balances).val))

private def execute (config : Json) : IO UInt32 := do
  unless (← get (config.getObjValAs? String "schema")) = "solcore-lean.value-contract-scenario.v1" do
    throw (IO.userError "unsupported value contract scenario schema")
  let funds ← get (requiredWord config "callerFunds")
  let slots ← get (observedSlots config)
  let constructor ← get (context (← get (config.getObjVal? "constructor")))
  unless constructor.caller != constructor.address do
    throw (IO.userError "caller and contract address must differ")
  let calls ← get (calls config constructor)
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
  let ledger := [(constructor.caller, funds)]
  let funded ← get (transfer ledger constructor.caller constructor.address constructor.value)
  let prepared ← lower (LinkedContract.prepareDeployment program.program deployPath images constructor.calldata
    {constructor with
      calldata := [], selfCodeAvailable := false, accounts := funded,
      balance := Core.WordMapping.lookupEntries constructor.address funded})
  let compiled ← lower (LinkedContract.compileObject program.program runtimePath images)
  let receipt := Contract.runWithReceipt prepared fuel
  let .returned deployed initialStorage := receipt.outcome | do
    report "deployment" (committedStorage slots [] :: undeclaredStorage slots [] ::
      committedBalance constructor.address ledger :: receiptFields receipt)
    return 1
  unless deployed == runtimeImage.bytes do
    report "deployment" [committedStorage slots [], undeclaredStorage slots [],
      committedBalance constructor.address ledger, ("status", "code-mismatch"), ("output", toJson (hex deployed))]
    return 1
  report "deployment" (committedStorage slots initialStorage :: undeclaredStorage slots initialStorage ::
    committedBalance constructor.address receipt.balances :: ("codeBytes", toJson deployed.length) :: receiptFields receipt)
  let mut storage := initialStorage
  let mut balances := receipt.balances
  let mut world := receipt.world
  for (call, index) in calls.zipIdx do
    let context := call.context
    let identity := [("index", toJson index), ("id", toJson call.id)]
    let .ok transferred := transfer balances context.caller context.address context.value | do
      report "execution" (identity ++ [("status", toJson "transfer-rejected"), ("detail", toJson "the ledger rejected the call value"),
        committedStorage slots storage, undeclaredStorage slots storage, committedBalance context.address balances])
      return 1
    let nonce := (world.find? (·.address == context.address)).map (·.nonce) |>.getD context.nonce
    let receipt := Contract.runWithReceipt (compiled.instantiate {context with
      storage := storage, world := world, nonce := nonce, accounts := transferred,
      balance := Core.WordMapping.lookupEntries context.address transferred}) fuel
    match receipt.outcome with
    | .returned _ nextStorage =>
        storage := nextStorage
        balances := receipt.balances
        world := receipt.world
    | _ => pure ()
    report "execution" (identity ++ committedStorage slots storage :: undeclaredStorage slots storage ::
      committedBalance context.address balances :: receiptFields receipt)
    match receipt.outcome with
    | .returned _ _ | .reverted _ => pure ()
    | _ => return 1
  return 0

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: rust-hull-value-scenario SCENARIO.json"
    return 2
  try execute (← get (Json.parse (← IO.FS.readFile path)))
  catch error =>
    report "preparation" [("status", "rejected"), ("detail", toJson error.toString)]
    return 1
