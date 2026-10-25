import Solcore.Synthesis.Core.StorageContract
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.TopLevelExecution
import Lean.Data.Json

/-! Execute the original checked Core contract over a persistent account world.
Each invocation starts a fresh Core heap. Only the public terminal `finalWorld`
is passed to the next transaction; suspended working state is never committed. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

def historySchema : String := "solcore-lean.storage-history.v1"
def bindingsSchema : String := "solcore-lean.storage-bindings.v1"

structure Transaction where
  id : String
  input : Word
  deriving BEq

structure Bindings where
  caller : Address
  address : Address

def fixtureBindings : Bindings := ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩

def bindingsJson (bindings : Bindings) : Json := Json.mkObj [
  ("schema", toJson bindingsSchema), ("caller", toJson (toString bindings.caller.val)),
  ("address", toJson (toString bindings.address.val))]

private def address (text : String) : Except String Address := do
  unless text.length ≤ 49 do throw "address is too long"
  let some value := text.toNat? | throw "invalid decimal address"
  unless toString value = text do throw "noncanonical decimal address"
  if bounded : value < addressModulus then return ⟨value, bounded⟩
  else throw "address exceeds 160 bits"

def decodeBindings (json : Json) : Except String Bindings := do
  unless (← json.getObjValAs? String "schema") = bindingsSchema do
    throw "unsupported storage bindings schema"
  let result : Bindings := ⟨← address (← json.getObjValAs? String "caller"),
    ← address (← json.getObjValAs? String "address")⟩
  unless result.caller != result.address do throw "caller and contract address must differ"
  unless json == bindingsJson result do throw "bindings differ from their canonical representation"
  return result

/-- The protocol always supplies the actual ABI selector and one big-endian
Word, rather than substituting the runtime input into the installed program. -/
def inputData (input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0xa4, 0x44, 0xf5, 0xe9] ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (input : Word) : String := encodeBytesText (inputData input).bytes

def initialWorldForContract (contract : CheckedCoreContract) (bindings : Bindings) : WorldState :=
  (WorldState.empty.putAccount bindings.caller Account.empty).putAccount bindings.address
    (Account.empty.withCode contract.code)

def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  initialWorldForContract plan.contract bindings

def storageJson (account : Account) : Json := toJson ([0, 1].map fun slot => Json.mkObj [
  ("slot", toJson (toString slot)),
  ("value", toJson (toString (account.storageRead (Word.ofNatModulo slot)).val))])

def zeroStorage : Json := storageJson Account.empty

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot accidentally install
a different contract or retain one invocation's local heap. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialStorage", initial),
    ("transactions", .arr rows), ("finalStorage", worldStorage world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.StorageExecution
