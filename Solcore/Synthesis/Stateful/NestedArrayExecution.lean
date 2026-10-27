import Solcore.Synthesis.Core.NestedArray
import Solcore.Synthesis.Stateful.StorageExecution

/-! Execute the original checked nested-array contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Calldata is the
canonical ABI encoding of `(flags, values)` for `uint256[][]`: the static head,
the outer offset 64, the outer length, one offset per row measured from the
start of that offset table, then each row's length and elements. Observations
report the nine declared slots; the Core account world is not enumerated. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.NestedArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)

def historySchema : String := "solcore-lean.nested-array-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  values : List (List Word)
  deriving BEq

private def words (values : List Word) : ByteArray :=
  values.foldl (fun bytes value => bytes ++ encodeWordBytesBE value) ByteArray.empty

/-- Row `i`'s offset from the start of the offset table: the table itself and
every earlier row's length Word and elements. -/
def rowOffsets (values : List (List Word)) : List Nat :=
  (values.zipIdx.map fun (_, index) =>
    32 * values.length + ((values.take index).map fun row => 32 + 32 * row.length).foldl (· + ·) 0)

/-- The selector of `run(uint256,uint256[][])`, the flags Word, the outer
offset 64 relative to the arguments, the outer length, the row offsets, then
each row's length and elements. -/
def inputBytes (flags : Word) (values : List (List Word)) : ByteArray :=
  values.foldl (fun bytes row => bytes ++ encodeWordBytesBE (Word.ofNatModulo row.length) ++ words row)
    (ByteArray.mk #[0x70, 0x95, 0xaf, 0xf8] ++ encodeWordBytesBE flags ++
      encodeWordBytesBE (Word.ofNatModulo 64) ++ encodeWordBytesBE (Word.ofNatModulo values.length) ++
      words ((rowOffsets values).map Word.ofNatModulo))

/-- Bounded cases are far below the Word-sized calldata limit; the check keeps
the runtime input total without assuming the case boundary. -/
def inputData? (flags : Word) (values : List (List Word)) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes flags values
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

def calldata (flags : Word) (values : List (List Word)) : String := encodeBytesText (inputBytes flags values)

/-- Slot zero holds the accumulator, slots one to six the per-element results,
slot seven the running row count and slot eight the running element count. -/
def observedSlots : List Word := (List.range (Solcore.Synthesis.Core.NestedArray.cellSlot + 1)).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap. A reverted invocation keeps the
prior committed world through the public runtime, not through this observer. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? transaction.flags transaction.values, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.NestedArrayExecution
