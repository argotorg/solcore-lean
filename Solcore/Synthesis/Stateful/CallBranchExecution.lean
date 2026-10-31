import Solcore.Synthesis.Core.CallBranch
import Solcore.Synthesis.Stateful.CallSequenceExecution

/-! Execute the original checked call-branch contracts over an account world.
The parent is installed as its call phase and the child as its contract; each
transaction runs through the public choice chain, which runs the call phase,
each child and each resume phase through the public top-level runner and
commits as one transaction. Only the chain's committed world becomes the next
transaction's world. Observations report each transaction's whole return data,
the parent's slots 0 to `B + 4P`, the child's slots 0 and 1, both balances and
both contracts' whole committed storage; no transaction commits a log.

`model` is a second account of the same sources, written over the bytes instead
of in Core: the child's data cut to its class byte's length, and the EVM's
return-data buffer as the parent's reads see it through its sites, with the
step evaluated alone in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.CallBranchExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.CallBranch (CheckedPlan Site)
open Solcore.Synthesis.Stateful.CallSequenceExecution (revertsOf lengthOf childData firstWord windowWord)

def historySchema : String := "solcore-lean.call-branch-history.v1"

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
  (List.range (CallBranch.parentSlotCount plan.sites)).map Word.ofNatModulo

def childSlots : List Word := (List.range CallBranch.childSlotCount).map Word.ofNatModulo

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

/-- Each transaction runs through the choice chain against the current
committed world; local heaps start fresh and only the committed world
persists. -/
def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let mut world := initialWorld plan bindings
  let initial := accountsJson plan world bindings
  let initialWhole := CallReturnExecution.wholeStorageJson world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match CallChoiceExecution.run (registry plan bindings) plan.parent world bindings.parent bindings.caller
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
      | .callLimit _ =>
          rows := rows.push (stoppedRow plan common "call-limit" world bindings)
          stopped := some transaction.id
  return Json.mkObj [("schema", toJson historySchema), ("bindings", NestedCallExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialAccounts", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalAccounts", accountsJson plan world bindings),
    ("finalAccountStorage", CallReturnExecution.wholeStorageJson world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

/-! ### The byte-level model -/

/-- The argument of position `position`: `mix·256` plus the input's byte
`position`. -/
def argumentOf (mix input : Word) (position : Nat) : Word :=
  mix * Word.ofNatModulo 256 + Word.ofNatModulo (input.val / 2 ^ (8 * position) % 256)

/-- Whether bit `bit` of `value` is set. -/
def bitOf (value : Word) (bit : Nat) : Bool := value.val / 2 ^ bit % 2 == 1

/-- A loop's limit: its two control bits' value, at most its bound. -/
def limitOf (input : Word) (index bound : Nat) : Nat := min (input.val / 2 ^ CallBranch.controlBit index % 4) bound

/-- One call's prescribed outcome: its position, whether it returned, and its
data's length. -/
structure CallRow where
  position : Nat
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

/-- The state of one transaction's walk through the sites. -/
private structure Walk where
  mix : Word
  child : List Word
  buffer : ByteArray
  written : List Word
  calls : Array CallRow

/-- The call at `position` in `site`: the child's step, writes and data, and the
four reads after the call. -/
private def callAt (plan : CheckedPlan) (fuel : Nat) (input : Word) (site : Site) (position : Nat) (walk : Walk) :
    Option Walk := do
  let x := argumentOf walk.mix input position
  let o := walk.child.getD 0 Word.zero
  let c := walk.child.getD 1 Word.zero + Word.ofNatModulo 1
  let r ← CallReturnExecution.stepResult plan.step fuel (x + o)
  let returned := !revertsOf x
  let data := childData r c x (lengthOf x)
  let ok := if returned then Word.ofNatModulo 1 else Word.zero
  let m := Word.ofNatModulo data.size
  let first := firstWord data
  let copied := windowWord data site.callWindow
  let slot := CallBranch.positionSlot plan.sites position
  let written := (((walk.written.set slot (ok + Word.ofNatModulo 2 * m)).set (slot + 1) first).set (slot + 2) m).set
    (slot + 3) copied
  return ⟨walk.mix + first + m + copied, if returned then [r, c] else walk.child, data, written,
    walk.calls.push ⟨position, returned, data.size⟩⟩

/-- Site `index`: the size before it, a branch's call when its bit is set or a
loop's calls while its counter is below its limit and the latest size differs
from its stop length, then the size and the exit window after it. -/
private def siteAt (plan : CheckedPlan) (fuel : Nat) (input : Word) (index : Nat) (site : Site) (start : Walk) :
    Option Walk := do
  let first := CallBranch.firstPosition plan.sites index
  let entered := start.written.set (CallBranch.siteSlot index) (Word.ofNatModulo start.buffer.size)
  let mut walk := { start with written := entered }
  match site.kind with
  | .branch =>
      if bitOf input (CallBranch.controlBit index) then
        walk ← callAt plan fuel input site first walk
  | .loop =>
      let limit := limitOf input index site.bound
      for counter in List.range site.bound do
        if counter < limit && walk.buffer.size != site.stop then
          walk ← callAt plan fuel input site (first + counter) walk
  let size := Word.ofNatModulo walk.buffer.size
  let copied := windowWord walk.buffer site.exitWindow
  let exited := (walk.written.set (CallBranch.siteSlot index + 1) size).set (CallBranch.siteSlot index + 2) copied
  return { walk with written := exited, mix := walk.mix + size + copied }

/-- The rows the sources prescribe: slot 0's accumulator and `z = 0`; each
site's reads and calls in program order, with the step evaluated alone; the
call count and the sum; and bit 30's revert, which keeps every prior slot. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let sites := plan.sites
  let count := CallBranch.parentSlotCount sites
  let mut parent : List Word := List.replicate count Word.zero
  let mut child : List Word := List.replicate CallBranch.childSlotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    let input := transaction.input
    let start := (List.replicate count Word.zero).set 0 (parent.getD 0 Word.zero + input)
    let mut walk : Walk :=
      ⟨Word.ofNatModulo (input.val / 2 ^ 32), child, ByteArray.empty, start, #[]⟩
    for (site, index) in sites.zipIdx do
      let some next := siteAt plan fuel input index site walk | return none
      walk := next
    let written := walk.written.set (CallBranch.countSlot sites) (Word.ofNatModulo walk.calls.size)
    let total := written.foldl (· + ·) Word.zero
    if bitOf input CallBranch.revertBit then
      rows := rows.push ⟨true, encodeWordBytesBE total, walk.calls.toList, parent, child⟩
    else
      parent := written
      child := walk.child
      rows := rows.push ⟨false, encodeWordBytesBE total, walk.calls.toList, parent, child⟩
  return some rows.toList

end Solcore.Synthesis.Stateful.CallBranchExecution
