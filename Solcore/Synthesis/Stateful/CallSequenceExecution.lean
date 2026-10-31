import Solcore.Synthesis.Core.CallSequence
import Solcore.Synthesis.Stateful.CallReturnExecution

/-! Execute the original checked call-sequence contracts over an account world.
The parent is installed as its call phase and the child as its contract; each
transaction runs through the public call chain, which runs the call phase, each
child and each resume phase through the public top-level runner and commits as
one transaction. Only the chain's committed world becomes the next
transaction's world. Observations report each transaction's whole return data,
the parent's slots 0 to `5n + 2` for `n` calls, the child's slots 0 and 1, both
balances and both contracts' whole committed storage; no transaction commits a
log.

`model` is a second account of the same sources, written over the bytes instead
of in Core: the child's data cut to its class byte's length, and the EVM's
return-data buffer as the parent's reads see it, with the step evaluated alone
in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallSequenceExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallSequence (CheckedPlan Window)

def historySchema : String := "solcore-lean.call-sequence-history.v1"

abbrev Bindings := NestedCallExecution.Bindings
abbrev Transaction := StorageExecution.Transaction

def inputData (bindings : Bindings) (input : Word) : HostStorageDriver.InputData :=
  NestedCallExecution.inputData bindings input

/-- The caller, the parent installed as its call phase and the child, all with
zero balance and empty storage. -/
def initialWorld (plan : CheckedPlan) (bindings : Bindings) : WorldState :=
  WorldState.empty
    |>.putAccount bindings.caller Account.empty
    |>.putAccount bindings.parent (Account.empty.withCode plan.callContract.code)
    |>.putAccount bindings.child (Account.empty.withCode plan.childContract.code)

/-- The child is the only contract a call resolves. -/
def registry (plan : CheckedPlan) (bindings : Bindings) : CheckedContractRegistry := {
  lookup := fun target => if target = bindings.child then some plan.childContract else none }

def parentSlots (plan : CheckedPlan) : List Word :=
  (List.range (CallSequence.parentSlotCount plan.calls)).map Word.ofNatModulo

def childSlots : List Word := (List.range CallSequence.childSlotCount).map Word.ofNatModulo

private def slotsJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)), ("value", toJson (toString (account.storageRead slot).val))])

private def accountJson (world : WorldState) (role : String) (address : Address) (slots : List Word) : Json :=
  match world.account? address with
  | none => Json.null
  | some account => Json.mkObj [
      ("role", toJson role), ("address", toJson (toString address.val)),
      ("balance", toJson (toString account.balance.val)), ("storage", slotsJson account slots)]

def accountsJson (plan : CheckedPlan) (world : WorldState) (bindings : Bindings) : Json := toJson [
  accountJson world "parent" bindings.parent (parentSlots plan), accountJson world "child" bindings.child childSlots]

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

private def stoppedRow (plan : CheckedPlan) (common : List (String × Json)) (status : String) (world : WorldState)
    (bindings : Bindings) : Json :=
  Json.mkObj (common ++ [("status", toJson status), ("committedAccounts", accountsJson plan world bindings),
    ("accountStorage", CallReturnExecution.wholeStorageJson world bindings), ("logs", Json.null)])

/-- Each transaction runs through the chain against the current committed
world; local heaps start fresh and only the committed world persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let mut world := initialWorld plan bindings
  let initial := accountsJson plan world bindings
  let initialWhole := CallReturnExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match CallChainExecution.run (registry plan bindings) plan.parent world bindings.parent bindings.caller
          (inputData bindings transaction.input) fuel with
      | .completed outcome finalWorld _ =>
          world := finalWorld
          rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
            ("committedAccounts", accountsJson plan world bindings),
            ("accountStorage", CallReturnExecution.wholeStorageJson world bindings),
            ("logs", toJson ([] : List Json))]))
          match outcome with
          | .trapped _ => stopped := some transaction.id
          | _ => pure ()
      | .outOfFuel _ =>
          rows := rows.push (stoppedRow plan common "out-of-fuel" world bindings)
          stopped := some transaction.id
      | .unresolved _ =>
          rows := rows.push (stoppedRow plan common "resolution-failure" world bindings)
          stopped := some transaction.id
      | .inputLimit _ =>
          rows := rows.push (stoppedRow plan common "input-limit" world bindings)
          stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson plan world bindings),
    ("finalAccountStorage", CallReturnExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

/-! ### The byte-level model -/

/-- A call's class byte: bit 0 reverts and the rest halves to the length. -/
def classOf (x : Word) : Nat := x.val % 256

def revertsOf (x : Word) : Bool := classOf x % 2 == 1

def lengthOf (x : Word) : Nat := min (classOf x / 2) CallSequence.capacity

/-- The argument of call `k`, from zero: `mix·256` plus the input's byte `k`. -/
def argumentOf (mix input : Word) (call : Nat) : Word :=
  mix * Word.ofNatModulo 256 + Word.ofNatModulo (input.val / 2 ^ (8 * call) % 256)

/-- The first `length` bytes of `d0 ‖ d1 ‖ d2`. -/
def childData (r c x : Word) (length : Nat) : ByteArray :=
  let multiplier := Word.ofNatModulo CallSequence.multiplier
  let d0 := r * multiplier
  let d1 := Word.ofNatModulo ((c * multiplier).val ^^^ x.val)
  let d2 := Word.ofNatModulo (d0.val ^^^ d1.val)
  (encodeWordBytesBE d0 ++ encodeWordBytesBE d1 ++ encodeWordBytesBE d2).extract 0 length

private def bigEndian (bytes : List UInt8) : Nat := bytes.foldl (fun total byte => total * 256 + byte.toNat) 0

/-- The data's first Word when they have one, otherwise zero. -/
def firstWord (data : ByteArray) : Word :=
  if data.size ≥ 32 then Word.ofNatModulo (bigEndian (data.extract 0 32).data.toList) else Word.zero

/-- The window's bytes left-aligned in a zero Word when they lie inside the
data, otherwise zero: what `returndatacopy` into a zeroed Word leaves. -/
def windowWord (data : ByteArray) (window : Window) : Word :=
  if window.offset + window.width ≤ data.size then
    Word.ofNatModulo (bigEndian (data.extract window.offset (window.offset + window.width)).data.toList *
      2 ^ (8 * (32 - window.width)))
  else Word.zero

/-- One call's prescribed outcome: whether it returned, and its data's length. -/
structure CallRow where
  returned : Bool
  length : Nat
  deriving BEq, Repr

/-- One modelled transaction: whether it reverts, its 32 output bytes, its calls'
prescribed outcomes, and the parent's and child's committed slots. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  calls : List CallRow
  parent : List Word
  child : List Word

/-- The rows the sources prescribe: the pre-call writes; per call the child's
step, writes and data, the reads before and after the call, the window and the
next argument; the re-read and the sum; and bit 24's revert, which keeps every
prior slot. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let count := plan.calls
  let mut parent : List Word := List.replicate (CallSequence.parentSlotCount count) Word.zero
  let mut child : List Word := List.replicate CallSequence.childSlotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    let input := transaction.input
    let accumulator := parent.getD 0 Word.zero + input
    let mut written := (parent.set 0 accumulator).set 1 Word.zero
    let mut state := child
    let mut total := accumulator
    let mut mix := Word.ofNatModulo (input.val / 2 ^ 32)
    let mut previous := Word.zero
    let mut copy : Option Word := none
    let mut calls : Array CallRow := #[]
    for (spot, index) in plan.windows.zipIdx do
      let x := argumentOf mix input index
      let o := state.getD 0 Word.zero
      let c := state.getD 1 Word.zero + Word.ofNatModulo 1
      let some r := CallReturnExecution.stepResult plan.step fuel (x + o) | return none
      let returned := !revertsOf x
      let data := childData r c x (lengthOf x)
      if returned then state := [r, c]
      let ok := if returned then Word.ofNatModulo 1 else Word.zero
      let m := Word.ofNatModulo data.size
      let first := firstWord data
      let copied := windowWord data spot
      if index == 0 && data.size ≥ 32 then copy := some first
      let slot := 5 * index + 2
      written := ((((written.set slot (ok + Word.ofNatModulo 2 * m)).set (slot + 1) first).set (slot + 2) previous).set
        (slot + 3) m).set (slot + 4) copied
      total := total + ok + Word.ofNatModulo 2 * m + first + previous + m + copied
      previous := m
      mix := mix + first + m + copied
      calls := calls.push ⟨returned, data.size⟩
    let again := (copy.map fun first => Word.ofNatModulo (count - 1) * first).getD Word.zero
    written := written.set (5 * count + 2) again
    total := total + again
    if input.val / 2 ^ 24 % 2 == 1 then
      rows := rows.push ⟨true, encodeWordBytesBE total, calls.toList, parent, child⟩
    else
      parent := written
      child := state
      rows := rows.push ⟨false, encodeWordBytesBE total, calls.toList, parent, child⟩
  return some rows.toList

end Solcore.Synthesis.Stateful.CallSequenceExecution
