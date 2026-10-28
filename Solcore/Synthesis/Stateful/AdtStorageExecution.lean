import Solcore.Abi.Keccak256
import Solcore.Synthesis.Core.AdtStorage
import Solcore.Synthesis.Stateful.KeyedStorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked enum and struct storage contract over a
persistent account world. A transaction calls one declared method with its
Word arguments in canonical calldata: the flags, then the key, the record
field and the variant where the method takes them, then the input unless it
reads. The observed slots are the accumulator, the enum and record fields'
slots and the entry slots of both mappings at the case's two keys, derived
with the separate `Solcore.Abi.V1.Keccak256` rather than the Core builders the
contract runs.

`model` is a second reading of the emitted source over a slot map: a write
stores its variant's tags and payload at the layout's offsets, a clear writes
the payload-free variant's tags alone, an update writes its field alone and a
read decodes the tags from the outermost level. It evaluates the step's Core
alone at each argument and shares nothing with the contract but that step and
the layout's sizes. Tests compare the two; neither is an oracle for the
differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.AdtStorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.AdtStorage (CheckedPlan Method Shape Payload)

def historySchema : String := "solcore-lean.adt-storage-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- A call of one method. Arguments the method does not take are zero. -/
structure Transaction where
  id : String
  method : Method
  flags : Word
  key : Word
  field : Nat
  variant : Nat
  input : Word
  deriving BEq

/-- The Word of each of the method's parameters, in order. -/
def arguments (tx : Transaction) : List Word :=
  tx.method.parameters.map fun
    | "key" => tx.key
    | "field" => Word.ofNatModulo tx.field
    | "variant" => Word.ofNatModulo tx.variant
    | "input" => tx.input
    | _ => tx.flags

/-- A transaction fits a plan when it calls a declared method, names one of the
case's keys, a record field and a variant of the shape where the method takes
them, and leaves every other argument zero. -/
def Transaction.valid (tx : Transaction) (plan : CheckedPlan) : Bool :=
  plan.methods.contains tx.method &&
    (if tx.method.keyed then plan.keys.contains tx.key else tx.key == Word.zero) &&
    (if tx.method.updates then tx.field < AdtStorage.recordFields else tx.field == 0) &&
    (if tx.method.takesVariant then tx.variant < plan.shape.count else tx.variant == 0) &&
    (!tx.method.reads || tx.input == Word.zero)

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

/-- The canonical calldata: the method's selector, then each argument Word. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (arguments tx).foldl (fun bytes value => bytes ++ encodeWordBytesBE value) (selectorBytes tx.method.selector)

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- The pinned std's first slot of `m[key]` for a mapping at base slot `base`:
`keccak256(base ++ key)`, from the independent ABI Keccak. -/
def entrySlot (base : Nat) (key : Word) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE (Word.ofNatModulo base) ++ encodeWordBytesBE key))).getD Word.zero

/-- `count` consecutive slots from `first`, wrapping as slot arithmetic does. -/
def region (first : Word) (count : Nat) : List Word :=
  (List.range count).map fun offset => first + Word.ofNatModulo offset

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The accumulator, the enum and record fields' slots, and each key's entry
slots in both mappings, in increasing numeric order without duplicates: every
slot the protocol writes, stale payload slots included. -/
def observedSlots (shape : Shape) (keys : List Word) : List Word :=
  ([Word.ofNatModulo AdtStorage.accumulatorSlot] ++
      region (Word.ofNatModulo AdtStorage.choiceSlot) shape.choiceSlots ++
      region (Word.ofNatModulo shape.recordSlot) shape.recordSlots ++
      keys.flatMap (fun key =>
        region (entrySlot shape.choiceMapSlot key) shape.choiceSlots ++
          region (entrySlot shape.recordMapSlot key) shape.recordSlots)).foldl
    (fun slots slot => insertSlot slot slots) []

def planSlots (plan : CheckedPlan) : List Word := observedSlots plan.shape plan.keys

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the storage profiles, with
each transaction's calldata selecting its method. -/
def observeContract (contract : CheckedCoreContract) (slots : List Word) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some input, some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := input }
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
              match terminal.outcome with
              | .trapped _ => stopped := some transaction.id
              | _ => pure ()
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson slots),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract (planSlots plan) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its result Word and the
slots it leaves committed as `(slot, value)` pairs. -/
structure ModelRow where
  reverted : Bool
  result : Word
  storage : List (Word × Word)
  deriving BEq

private def lookup (storage : List (Word × Word)) (slot : Word) : Word :=
  ((storage.find? fun (candidate, _) => candidate == slot).map Prod.snd).getD Word.zero

private def update (storage : List (Word × Word)) (slot value : Word) : List (Word × Word) :=
  (slot, value) :: storage.filter fun (candidate, _) => candidate != slot

private def multiplier : Word := Word.ofNatModulo AdtStorage.multiplier

/-- The Word written at offset `offset` of a value written with `result`. -/
private def written (result : Word) (offset : Nat) : Word := result + Word.ofNatModulo offset * multiplier

/-- Variant `variant` of the shape's enum written at `first`: one at each outer
level, zero at its own level unless it is the last variant, then its payload,
each payload Word at offset `o` from `origin` holding `result + o·K`. -/
private def writeChoice (shape : Shape) (storage : List (Word × Word)) (first : Word) (origin variant : Nat)
    (result : Word) : List (Word × Word) := Id.run do
  let count := shape.count
  let mut current := storage
  for level in List.range (min variant (count - 1)) do
    current := update current (first + Word.ofNatModulo level) (Word.ofNatModulo 1)
  let payload := if variant + 1 < count then
      (update current (first + Word.ofNatModulo variant) Word.zero, variant + 1)
    else (current, count - 1)
  current := payload.1
  for index in List.range (shape.width variant) do
    let offset := payload.2 + index
    current := update current (first + Word.ofNatModulo offset) (written result (origin + offset))
  return current

/-- The decoded variant at `first` and its payload Words: the outermost zero
tag selects its level's variant, and past every level the last one. -/
private def readChoice (shape : Shape) (storage : List (Word × Word)) (first : Word) : List Word := Id.run do
  let count := shape.count
  for level in List.range (count - 1) do
    if lookup storage (first + Word.ofNatModulo level) == Word.zero then
      return [Word.ofNatModulo level] ++ (List.range (shape.width level)).map fun index =>
        lookup storage (first + Word.ofNatModulo (level + 1 + index))
  return [Word.ofNatModulo (count - 1)] ++ (List.range (shape.width (count - 1))).map fun index =>
    lookup storage (first + Word.ofNatModulo (count - 1 + index))

/-- The record's field `field` at `first`, written as a whole-record write writes it. -/
private def writeField (shape : Shape) (storage : List (Word × Word)) (first : Word) (field variant : Nat)
    (result : Word) : List (Word × Word) :=
  let offset := shape.fieldOffset field
  if field == shape.position then writeChoice shape storage (first + Word.ofNatModulo offset) offset variant result
  else update storage (first + Word.ofNatModulo offset) (written result offset)

private def readRecord (shape : Shape) (storage : List (Word × Word)) (first : Word) : List Word :=
  (List.range AdtStorage.recordFields).flatMap fun field =>
    let slot := first + Word.ofNatModulo (shape.fieldOffset field)
    if field == shape.position then readChoice shape storage slot else [lookup storage slot]

/-- Horner's rule over the decoded Words with the multiplier. -/
def digest (tokens : List Word) : Word := tokens.foldl (fun total token => total * multiplier + token) Word.zero

def modelTransaction (plan : CheckedPlan) (fuel : Nat) (prior : List (Word × Word)) (tx : Transaction) :
    Option ModelRow := do
  let shape := plan.shape
  let accumulator := Word.ofNatModulo AdtStorage.accumulatorSlot
  let first : Word :=
    if tx.method.keyed then entrySlot (if tx.method.record then shape.recordMapSlot else shape.choiceMapSlot) tx.key
    else Word.ofNatModulo (if tx.method.record then shape.recordSlot else AdtStorage.choiceSlot)
  let (result, storage) ← if tx.method.reads then
      let tokens := if tx.method.record then readRecord shape prior first else readChoice shape prior first
      pure (digest tokens, prior)
    else do
      let result ← stepResult plan.step fuel (tx.input + lookup prior accumulator)
      let storage :=
        if tx.method.clears then writeChoice shape prior first 0 shape.clearVariant result
        else if !tx.method.record then writeChoice shape prior first 0 tx.variant result
        else if tx.method.updates then writeField shape prior first tx.field tx.variant result
        else (List.range AdtStorage.recordFields).foldl
          (fun current field => writeField shape current first field tx.variant result) prior
      pure (result, storage)
  let reverted := tx.flags.val % 2 == 1
  return ⟨reverted, result, if reverted then prior else update storage accumulator result⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (plan : CheckedPlan) (fuel : Nat) (transactions : List Transaction) : Option (List ModelRow) := Id.run do
  let mut storage : List (Word × Word) := []
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction plan fuel storage transaction with
    | some row =>
        rows := rows.push row
        storage := row.storage
    | none => return none
  return some rows.toList

/-- A modelled row's value at each observed slot. -/
def modelSlots (row : ModelRow) (slots : List Word) : List Word := slots.map (lookup row.storage)

end Solcore.Synthesis.Stateful.AdtStorageExecution
