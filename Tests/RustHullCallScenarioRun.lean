import Solcore.Frontend.RustHull.Decode
import Solcore.Frontend.RustHull.LinkedContract
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the fixed two-contract value/log protocol from actual linked Hull.
Both constructors must return their exact runtime images. Transaction rows use
the complete shared world on success and the prior world on root revert; failed
receipts never supply invented committed balances or account snapshots. -/
set_option autoImplicit false
open Lean Solcore Solcore.Frontend.RustHull Solcore.Synthesis.Stateful

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def lower {α : Type} (result : LowerM α) : IO α :=
  get (result.mapError (fun error => reprStr error))

private def exactFields (json : Json) (names : List String) : Except String Unit := do
  let .obj fields := json | throw "expected a JSON object"
  let actual := fields.toList.map Prod.fst
  unless actual.length == names.length && actual.all names.contains do
    throw s!"object fields must be exactly {reprStr names}"

private def word (json : Json) (key : String) : Except String Core.Word := do
  let text ← json.getObjValAs? String key
  unless !text.isEmpty && text.length ≤ 78 && text.toList.all (fun c => '0' ≤ c && c ≤ '9') do
    throw s!"{key} must be a canonical decimal Word"
  let some natural := text.toNat? | throw s!"invalid {key}"
  unless toString natural == text do throw s!"noncanonical {key}"
  let some value := Core.Word.ofNat? natural | throw s!"{key} exceeds a Word"
  pure value

private def address (json : Json) (key : String) : Except String Core.Word := do
  let value ← word json key
  unless value.val < 2 ^ 160 do throw s!"{key} exceeds 160 bits"
  pure value

private def hex (value : List UInt8) : String :=
  "0x" ++ String.ofList (value.flatMap fun byte =>
    ["0123456789abcdef".toList[byte.toNat / 16]!, "0123456789abcdef".toList[byte.toNat % 16]!])

private def calldata (child input : Core.Word) : List UInt8 :=
  [0x73, 0x57, 0xf5, 0xd2] ++
    (ContractRuntime.encodeWordBytesBE child).data.toList ++
    (ContractRuntime.encodeWordBytesBE input).data.toList

private structure Bindings where
  caller : Core.Word
  parent : Core.Word
  child : Core.Word

private structure Call where
  id : String
  input : Core.Word
  data : List UInt8

private structure Config where
  hull : String
  images : String
  bindings : Bindings
  parentDeployPath : List String
  parentRuntimePath : List String
  childDeployPath : List String
  childRuntimePath : List String
  fuel : Nat
  availableGas : Core.Word
  calls : List Call

private def fixedPath (json : Json) (key : String) (expected : List String) : Except String (List String) := do
  let actual ← json.getObjValAs? (List String) key
  unless actual == expected do throw s!"{key} differs from the fixed call profile"
  pure actual

/-- All configuration and ABI validation precedes even constructor execution. -/
private def decodeConfig (json : Json) : Except String Config := do
  exactFields json ["schema", "hull", "images", "bindings", "parentDeployPath", "parentRuntimePath",
    "childDeployPath", "childRuntimePath", "initialBalances", "observedSlots", "fuel", "availableGas", "calls"]
  unless (← json.getObjValAs? String "schema") == "solcore-lean.call-contract-scenario.v1" do
    throw "unsupported call scenario schema"
  let bindings ← json.getObjVal? "bindings"
  exactFields bindings ["schema", "caller", "parent", "child"]
  unless (← bindings.getObjValAs? String "schema") == "solcore-lean.call-bindings.v1" do
    throw "unsupported call bindings schema"
  let bindings : Bindings := ⟨← address bindings "caller", ← address bindings "parent", ← address bindings "child"⟩
  unless bindings.caller != bindings.parent && bindings.caller != bindings.child &&
      bindings.parent != bindings.child && bindings.parent.val > 17 && bindings.child.val > 17 &&
      bindings.parent.val != 256 && bindings.child.val != 256 do
    throw "caller, parent and child must be distinct; contract addresses must exceed 17 and differ from 256"
  let balances ← json.getObjVal? "initialBalances"
  exactFields balances ["parent", "child"]
  unless (← balances.getObjValAs? String "parent") == "8" &&
      (← balances.getObjValAs? String "child") == "0" do
    throw "initial contract balances must be parent 8 and child 0"
  unless (← json.getObjValAs? (List String) "observedSlots") == ["0", "1"] do
    throw "observedSlots must be exactly [0,1]"
  let fuel ← json.getObjValAs? Nat "fuel"
  unless 0 < fuel && fuel ≤ 1000000000 do throw "fuel must be between 1 and 1000000000"
  let availableGas ← word json "availableGas"
  unless availableGas.val > 0 do throw "availableGas must be positive"
  let values ← json.getObjValAs? (List Json) "calls"
  unless 1 ≤ values.length && values.length ≤ 3 do throw "call scenarios require one to three transactions"
  let calls ← values.foldlM (init := ([] : List Call)) fun prior value => do
    exactFields value ["id", "input", "calldata", "value", "persist"]
    let id ← value.getObjValAs? String "id"
    unless !id.isEmpty && id.length ≤ 64 && id.toList.all (fun c =>
        ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-') do
      throw "transaction IDs must be bounded ASCII identifiers"
    if prior.any (·.id == id) then throw "duplicate transaction ID"
    let input ← word value "input"
    let data := calldata bindings.child input
    unless (← value.getObjValAs? String "calldata") == hex data do
      throw "calldata differs from the exact selector, bound child address and original input"
    unless (← value.getObjValAs? String "value") == "0" && (← value.getObjValAs? Bool "persist") do
      throw "transactions must have zero top-level value and persist"
    pure (prior ++ [⟨id, input, data⟩])
  return {
    hull := ← json.getObjValAs? String "hull"
    images := ← json.getObjValAs? String "images"
    bindings
    parentDeployPath := ← fixedPath json "parentDeployPath" ["SynthesizedCallerDeploy"]
    parentRuntimePath := ← fixedPath json "parentRuntimePath" ["SynthesizedCallerDeploy", "SynthesizedCaller"]
    childDeployPath := ← fixedPath json "childDeployPath" ["SynthesizedCalleeDeploy"]
    childRuntimePath := ← fixedPath json "childRuntimePath" ["SynthesizedCalleeDeploy", "SynthesizedCallee"]
    fuel, availableGas, calls
  }

private def outcomeFields : Contract.Outcome → List (String × Json)
  | .returned data _ => [("status", "returned"), ("output", toJson (hex data))]
  | .reverted data => [("status", "reverted"), ("output", toJson (hex data))]
  | .invalid => [("status", "invalid")]
  | .outOfFuel _ => [("status", "out-of-fuel")]
  | .languageFailure reason => [("status", "language-failure"), ("detail", toJson (reprStr reason))]
  | .coreFault error => [("status", "core-fault"), ("detail", toJson (reprStr error))]
  | .exportError error => [("status", "export-error"), ("detail", toJson error)]

private def report (stage : String) (fields : List (String × Json)) : IO Unit :=
  IO.println ((Json.mkObj (("stage", toJson stage) :: fields)).compress)

private def storageJson (entries : Core.WordMapping.Entries) : Json :=
  toJson ([0, 1].map fun slot => Json.mkObj [
    ("slot", toJson (toString slot)),
    ("value", toJson (toString (Core.WordMapping.lookupEntries (Core.Word.ofNatModulo slot) entries).val))])

private def accountJson (role : String) (account : AccountState.Account) (balances : Core.WordMapping.Entries) : Json :=
  Json.mkObj [("role", toJson role), ("address", toJson (toString account.address.val)),
    ("balance", toJson (toString (Core.WordMapping.lookupEntries account.address balances).val)),
    ("storage", storageJson account.storage)]

private def snapshot (bindings : Bindings) (world : List AccountState.Account)
    (balances : Core.WordMapping.Entries) : Except String Json := do
  let some parent := world.find? (·.address == bindings.parent) | throw "committed parent account missing"
  let some child := world.find? (·.address == bindings.child) | throw "committed child account missing"
  unless world.length == 2 do throw "committed world contains unexpected accounts"
  unless balances.all (fun entry => entry.1 == bindings.parent || entry.1 == bindings.child ||
      entry.1 == bindings.caller) do
    throw "committed ledger contains unexpected accounts"
  unless (balances.map Prod.fst).eraseDups.length == balances.length do throw "duplicate committed ledger entry"
  pure (toJson [accountJson "parent" parent balances, accountJson "child" child balances])

/-- Both contracts' whole committed storage, canonicalized from their entries. -/
private def wholeStorage (bindings : Bindings) (world : List AccountState.Account) : Json :=
  let roles : List (String × Core.Word) := [("parent", bindings.parent), ("child", bindings.child)]
  toJson (roles.map fun (role, address) =>
    match world.find? (fun (account : AccountState.Account) => account.address == address) with
    | some account => AccountStorage.hullAccountJson role address account.storage
    | none => Json.null)

private def logsJson (logs : List Logs.Event) : Json :=
  toJson (logs.map fun event => Json.mkObj [("address", toJson (toString event.address.val)),
    ("topics", toJson (event.topics.map (fun value => toString value.val))), ("data", toJson (hex event.data))])

/-- As for ordinary Hull top-level execution, supply the entry ledger after
checked value transfer. Constructor execution itself observes this value and
ledger; a failed constructor is never installed or assigned fixture balances. -/
private def transfer (balances : Core.WordMapping.Entries) (source target amount : Core.Word) :
    Except String Core.WordMapping.Entries := do
  let before := Core.WordMapping.lookupEntries source balances
  let recipient := Core.WordMapping.lookupEntries target balances
  unless amount.val ≤ before.val do throw "constructor caller has insufficient balance"
  let some credited := Core.Word.ofNat? (recipient.val + amount.val) | throw "constructor balance overflow"
  pure (Core.WordMapping.insertEntries target credited
    (Core.WordMapping.insertEntries source (Core.Word.ofNatModulo (before.val - amount.val)) balances))

private def deploy (stage : String) (prepared : Contract.Prepared) (image : CodeImage.Image)
    (target : Core.Word) (allowed : List Core.Word) (fuel : Nat) :
    IO (Option (List AccountState.Account × Core.WordMapping.Entries)) := do
  let receipt := Contract.runWithReceipt prepared fuel
  let .returned bytes storage := receipt.outcome | do
    report stage (("imageVerified", toJson false) :: outcomeFields receipt.outcome)
    return none
  unless bytes == image.bytes do
    report stage [("status", "code-mismatch"), ("output", toJson (hex bytes)), ("imageVerified", toJson false)]
    return none
  let some account := receipt.world.find? (·.address == target) | do
    report stage [("status", "export-error"), ("detail", "deployment account is absent")]
    return none
  unless storage.all (fun entry => entry.2 == Core.Word.zero) && receipt.logs.isEmpty &&
      receipt.world.length == allowed.length &&
      receipt.world.all (fun entry => allowed.contains entry.address && !entry.destroyed &&
        entry.storage.all (fun value => value.2 == Core.Word.zero)) do
    report stage [("status", "profile-mismatch"), ("detail", "fixed constructors must leave empty storage and logs")]
    return none
  report stage (("imageVerified", toJson true) :: ("codeBytes", toJson bytes.length) :: outcomeFields receipt.outcome)
  let installed := {account with storage := storage, code := some bytes, transient := [], created := false, destroyed := false}
  return some (receipt.world.map (fun entry => if entry.address == target then installed else entry), receipt.balances)

private def execute (json : Json) : IO UInt32 := do
  let config ← get (decodeConfig json)
  let program ← get ((decodeText (← IO.FS.readFile config.hull)).mapError reprStr)
  let images ← get (CodeImage.decode (← IO.FS.readFile config.images))
  let parentImage ← get (CodeImage.select images config.parentRuntimePath)
  let childImage ← get (CodeImage.select images config.childRuntimePath)
  let initialContext (target : Core.Word) : Contract.Context := {
    caller := config.bindings.caller, address := target, availableGas := some config.availableGas }
  let initialLedger := [(config.bindings.caller, Core.Word.ofNatModulo 8),
    (config.bindings.parent, Core.Word.zero), (config.bindings.child, Core.Word.zero)]
  let childPrepared ← lower (LinkedContract.prepareDeployment program.program config.childDeployPath images []
    {(initialContext config.bindings.child) with accounts := initialLedger})
  let parentCompiled ← lower (LinkedContract.compileObject program.program config.parentRuntimePath images)
  let some (childWorld, childLedger) ← deploy "deployment-child" childPrepared childImage
    config.bindings.child [config.bindings.child] config.fuel | return 1
  let funded ← get (transfer childLedger config.bindings.caller config.bindings.parent (Core.Word.ofNatModulo 8))
  let parentPrepared ← lower (LinkedContract.prepareDeployment program.program config.parentDeployPath images []
    {(initialContext config.bindings.parent) with
      world := childWorld
      accounts := funded
      value := Core.Word.ofNatModulo 8
      balance := Core.WordMapping.lookupEntries config.bindings.parent funded})
  let some (deployedWorld, deployedLedger) ← deploy "deployment-parent" parentPrepared parentImage
    config.bindings.parent [config.bindings.parent, config.bindings.child] config.fuel | return 1
  unless Core.WordMapping.lookupEntries config.bindings.parent deployedLedger == Core.Word.ofNatModulo 8 &&
      Core.WordMapping.lookupEntries config.bindings.child deployedLedger == Core.Word.zero &&
      Core.WordMapping.lookupEntries config.bindings.caller deployedLedger == Core.Word.zero do
    throw (IO.userError "constructor receipts differ from the fixed initial balances")
  let some deployedChild := deployedWorld.find? (·.address == config.bindings.child) |
    throw (IO.userError "deployed child is missing")
  unless deployedChild.code == some childImage.bytes do throw (IO.userError "child runtime image changed during parent deployment")
  let mut world := deployedWorld
  let mut balances := deployedLedger
  let mut committed ← get (snapshot config.bindings world balances)
  let mut whole := wholeStorage config.bindings world
  report "initialization" [("committedAccounts", committed), ("accountStorage", whole)]
  for (call, index) in config.calls.zipIdx do
    let some current := world.find? (·.address == config.bindings.parent) |
      throw (IO.userError "committed parent account missing before call")
    let receipt := Contract.runWithReceipt (parentCompiled.instantiate {
      (initialContext config.bindings.parent) with
      calldata := call.data, storage := current.storage, nonce := current.nonce,
      world, accounts := balances, balance := Core.WordMapping.lookupEntries config.bindings.parent balances }) config.fuel
    let identity := [("id", toJson call.id), ("index", toJson index)]
    match receipt.outcome with
    | .returned _ _ =>
        match snapshot config.bindings receipt.world receipt.balances with
        | .error error =>
            report "execution" (identity ++ [("status", toJson "export-error"), ("detail", toJson error),
              ("committedAccounts", committed), ("accountStorage", whole), ("logs", Json.null)])
            return 1
        | .ok next =>
            world := receipt.world
            balances := receipt.balances
            committed := next
            whole := wholeStorage config.bindings receipt.world
            report "execution" (identity ++ outcomeFields receipt.outcome ++
              [("committedAccounts", committed), ("accountStorage", whole), ("logs", logsJson receipt.logs)])
    | .reverted _ =>
        report "execution" (identity ++ outcomeFields receipt.outcome ++
          [("committedAccounts", committed), ("accountStorage", whole), ("logs", toJson ([] : List Json))])
    | _ =>
        report "execution" (identity ++ outcomeFields receipt.outcome ++
          [("committedAccounts", committed), ("accountStorage", whole), ("logs", Json.null)])
        return 1
  return 0

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: rust-hull-call-scenario SCENARIO.json"
    return 2
  try execute (← get (Json.parse (← IO.FS.readFile path)))
  catch error =>
    report "preparation" [("status", "rejected"), ("detail", toJson error.toString)]
    return 1
