import Solcore.Synthesis.Core.NestedCall
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.ContractRuntime.OneLevelNestedExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Original checked-Core execution of a fixed parent/leaf protocol. Only the
public scheduler's committed world and transaction journal leave an invocation.
Exhausted working state and speculative logs are never reported as committed.
Both contracts' whole committed storage is reported with their slots zero and one. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.NestedCallExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.NestedCall (CheckedPlan)

abbrev Transaction := StorageExecution.Transaction

def historySchema : String := "solcore-lean.call-history.v2"
def bindingsSchema : String := "solcore-lean.call-bindings.v1"

structure Bindings where
  caller : Address
  parent : Address
  child : Address

def fixtureBindings : Bindings := ⟨⟨17, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩⟩

def bindingsJson (bindings : Bindings) : Json := Json.mkObj [
  ("schema", toJson bindingsSchema), ("caller", toJson (toString bindings.caller.val)),
  ("parent", toJson (toString bindings.parent.val)), ("child", toJson (toString bindings.child.val))]

private def address (text : String) : Except String Address := do
  unless text.length ≤ 49 do throw "address is too long"
  let some value := text.toNat? | throw "invalid decimal address"
  unless toString value = text do throw "noncanonical decimal address"
  if bounded : value < addressModulus then return ⟨value, bounded⟩
  else throw "address exceeds 160 bits"

def decodeBindings (json : Json) : Except String Bindings := do
  unless (← json.getObjValAs? String "schema") = bindingsSchema do throw "unsupported call bindings schema"
  let result : Bindings := ⟨← address (← json.getObjValAs? String "caller"),
    ← address (← json.getObjValAs? String "parent"), ← address (← json.getObjValAs? String "child")⟩
  unless result.caller != result.parent && result.caller != result.child && result.parent != result.child do
    throw "caller, parent and child must be distinct"
  unless result.parent.val > 17 && result.child.val > 17 &&
      result.parent.val != 256 && result.child.val != 256 do
    throw "contracts must not use precompile addresses"
  unless json == bindingsJson result do throw "bindings differ from their canonical representation"
  return result

/-- Bind the actual child address at execution time, leaving both stored Core
programs and emitted source independent of deployment addresses. -/
def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++
    encodeWordBytesBE (addressToWord bindings.child) ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (bindings : Bindings) (input : Word) : String := encodeBytesText (inputData bindings input).bytes

def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller Account.empty
    |>.putAccount bindings.parent ((Account.empty.withCode plan.parentContract.code).withBalance (Word.ofNatModulo 8))
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

private def accountJson (world : WorldState) (role : String) (address : Address) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", StorageExecution.storageJson account)]

def accountsJson (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent, accountJson world "child" bindings.child]

/-- Both contracts' whole committed storage, in role order. -/
def wholeStorageJson (world : WorldState) (bindings : Bindings) : Json :=
  AccountStorage.worldJson world [("parent", bindings.parent), ("child", bindings.child)]

def logsJson (journal : TransactionJournal) : Json := toJson (journal.logList.map fun entry => Json.mkObj [
  ("address", toJson (toString entry.emitter.val)),
  ("topics", toJson [toString entry.topic.val]),
  ("data", toJson (encodeBytesText (encodeWordBytesBE entry.payload)))])

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Each transaction resolves the root against the current committed world;
the scheduler resolves the child at its actual call boundary. Local heaps and
transaction journals start fresh, while the selected world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.parent then some plan.parentContract
      else if target = bindings.child then some plan.childContract else none }
  let mut world := initialWorld plan bindings
  let initial := accountsJson world bindings
  let initialWhole := wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.parent, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData bindings transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.parent with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [("status", toJson "resolution-failure"),
            ("committedAccounts", accountsJson prior bindings), ("accountStorage", wholeStorageJson prior bindings),
            ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match (OneLevelNestedExecution.run resolved invocation installed registry fuel).view with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedAccounts", accountsJson world bindings), ("accountStorage", wholeStorageJson world bindings),
                ("logs", logsJson terminal.committedJournal)]))
              match terminal.outcome with
              | .trapped _ => stopped := some transaction.id
              | _ => pure ()
          | .outOfFuel _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [("status", toJson "out-of-fuel"),
                ("committedAccounts", accountsJson prior bindings), ("accountStorage", wholeStorageJson prior bindings),
            ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson world bindings),
    ("finalAccountStorage", wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

end Solcore.Synthesis.Stateful.NestedCallExecution
