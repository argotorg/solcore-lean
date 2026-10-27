import Solcore.Abi.Keccak256
import Solcore.Synthesis.Core.ContractMethods
import Solcore.Synthesis.Stateful.StdCalldata
import Solcore.Synthesis.Stateful.StorageExecution
import Solcore.Synthesis.Stateful.AccountStorage

/-! Execute the original checked several-methods contract over a persistent
account world. A method has a name and a number of uint256 parameters; its
selector is the first four bytes of the Keccak-256 of its signature. A
transaction calls one method with its Word inputs in canonical calldata, or
sends a missing selector, matching no method, with one Word. `stdDispatch` is
a second model of the pinned std's dispatcher, written over the bytes instead
of in Core, which prescribes each transaction's outcome. Observations report
slots zero to five and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MethodsExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.ContractMethods (CheckedPlan Shape)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError)

def historySchema : String := "solcore-lean.methods-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Method where
  name : String
  arity : Nat
  deriving BEq, Repr

def Method.signature (method : Method) : String :=
  method.name ++ "(" ++ ",".intercalate (List.replicate method.arity "uint256") ++ ")"

/-- The first four bytes of a signature's Keccak-256, as std's `Selector`
computes them and the compiler checks them for collisions. -/
def selectorOf (signature : String) : Nat :=
  StdCalldata.bigEndian (Solcore.Abi.V1.Keccak256.hash signature.toUTF8) 0 4

def Method.selector (method : Method) : Nat := selectorOf method.signature

def Method.shape (method : Method) : Shape := ⟨method.selector, method.arity⟩

/-- A call of method `target` with its inputs, or, without a target, the
missing selector with one Word. -/
structure Transaction where
  id : String
  target : Option Nat
  inputs : List Word
  deriving BEq

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

/-- The selector a transaction sends. -/
def sentSelector (methods : List Method) (missing : Nat) (tx : Transaction) : Nat :=
  match tx.target with
  | some position => (methods.getD position ⟨"", 0⟩).selector
  | none => missing

/-- The canonical calldata: the selector, then each input Word. -/
def inputBytes (methods : List Method) (missing : Nat) (tx : Transaction) : ByteArray :=
  tx.inputs.foldl (fun bytes value => bytes ++ encodeWordBytesBE value)
    (selectorBytes (sentSelector methods missing tx))

/-- A call names a declared method and carries exactly its arguments; the
missing selector carries one Word. -/
def Transaction.valid (tx : Transaction) (methods : List Method) : Bool :=
  match tx.target with
  | some position => position < methods.length && tx.inputs.length == (methods.getD position ⟨"", 0⟩).arity
  | none => tx.inputs.length == 1

/-- The pinned std's dispatch over raw calldata: the position of the method that
runs, or the rejecting error selector. Calldata shorter than four bytes or with
no matching selector reaches the default fallback; the first method whose
selector matches, in declaration order, runs once its arguments' head exists. -/
def stdDispatch (shapes : List Shape) (input : ByteArray) : Except Nat Nat :=
  if input.size < 4 then .error noSelectorError
  else
    let selector := StdCalldata.bigEndian input 0 4
    match shapes.zipIdx.find? (fun (shape, _) => shape.selector == selector) with
    | none => .error noSelectorError
    | some (shape, position) =>
        if input.size < 4 + 32 * shape.arity then .error truncatedError else .ok position

def stdRejection? (shapes : List Shape) (input : ByteArray) : Option Nat :=
  match stdDispatch shapes input with
  | .error selector => some selector
  | .ok _ => none

def calldata (methods : List Method) (missing : Nat) (tx : Transaction) : String :=
  encodeBytesText (inputBytes methods missing tx)

def inputData? (methods : List Method) (missing : Nat) (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes methods missing tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

/-- Slot zero holds the shared accumulator, slot one the shared call count and
slots two to five the methods' accumulators. -/
def observedSlots : List Word :=
  (List.range Solcore.Synthesis.Core.ContractMethods.slotCount).map Word.ofNatModulo

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

/-- Independent original-Core observation, as for the storage profiles, with
each transaction's calldata selecting its method. -/
def observeContract (contract : CheckedCoreContract) (methods : List Method) (missing : Nat)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := StorageExecution.initialWorldForContract contract bindings
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? methods missing transaction, registry.resolve? prior bindings.address with
      | none, _ =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "input-limit"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | _, none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
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
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (methods : List Method) (missing : Nat) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract methods missing transactions bindings fuel

end Solcore.Synthesis.Stateful.MethodsExecution
