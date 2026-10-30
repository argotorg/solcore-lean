import Solcore.Synthesis.Core.ConstructorArguments
import Solcore.Synthesis.Stateful.EnumArgumentExecution

/-! Execute the original checked constructor-argument contracts over an account
world. The deployment phase installs the initializer at the bound address and
runs it as one top-level invocation whose input data are the constructor's
argument bytes: canonical, or with one malformation. On return the account's
code becomes the runtime contract's through `Account.withCode`, which keeps
the storage the initializer wrote; a revert installs nothing and ends the
scenario. Runtime transactions then run as for the storage profiles, each
invocation with a fresh Core heap, and only the public terminal `finalWorld`
becomes the next transaction's world. Observations report the deployment row,
then each transaction's whole return data, slots zero to five and the
contract's whole committed storage.

`stdDecide` is a second model of the pinned std's decision on the argument
bytes, written over the bytes instead of in Core: the compiler's generated copy
and std's `MemoryWordReader`, reading from 0 with no up-front head check, each
read and advance bounded by the argument size. `model` reads the emitted
source on its decision, with the step evaluated alone in Core. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.ConstructorArgumentsExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.ConstructorArguments (CheckedPlan Parameters)
open Solcore.Synthesis.Core.EnumArgument (Constructor Payload Shape)
open Solcore.Synthesis.Core.StdDispatch (truncatedError)

def historySchema : String := "solcore-lean.constructor-argument-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- The longest canonical `bytes` payload. -/
def maxLength : Nat := 64

/-- How the arguments depart from their canonical encoding: a cut, trailing
bytes, the head's offset Word, a `bytes` length Word, an unknown tag (whole, or
cut right after it), a dynamic enum's `bytes` tail offset, or a static enum cut
to the chosen constructor's head. -/
inductive Malformation where
  | none
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | tag (value : Word)
  | tagCut (value : Word)
  | tail (value : Word)
  | narrow
  deriving BEq, Repr

/-- The deployment record: the leading Word `a`, the enum choice, the second
Word or field Words `first` and `second`, a `bytes` length, and the
malformation. -/
structure Deployment where
  a : Word
  choice : Nat
  first : Word
  second : Word
  length : Nat
  malformation : Malformation
  deriving BEq

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The enum choice as an argument-profile transaction, whose body encoder and
decoder are reused. -/
def enumTransaction (deployment : Deployment) : EnumArgumentExecution.Transaction :=
  ⟨"deployment", Word.zero, deployment.choice, deployment.first, deployment.second, deployment.length, .none⟩

/-- A `bytes` payload: the first `length` bytes of `first · K` and
`second · K`. -/
def payload (deployment : Deployment) : ByteArray :=
  EnumArgumentExecution.payload deployment.first deployment.second deployment.length

private def zeros (count : Nat) : ByteArray := ByteArray.mk (Array.replicate count 0)

private def w (value : Nat) : ByteArray := encodeWordBytesBE (Word.ofNatModulo value)

/-- Where an enum's body starts: inline at 32 for a static enum, at the
canonical offset 64 for a dynamic one. -/
def bodyStart (shape : Shape) : Nat := if shape.dynamic then 64 else 32

/-- The canonical argument bytes. -/
def canonicalBytes (parameters : Parameters) (deployment : Deployment) : ByteArray :=
  match parameters with
  | .none => ByteArray.empty
  | .word => encodeWordBytesBE deployment.a
  | .words => encodeWordBytesBE deployment.a ++ encodeWordBytesBE deployment.first
  | .bytes => encodeWordBytesBE deployment.a ++ w 64 ++ w deployment.length ++ payload deployment ++
      zeros (EnumArgumentExecution.paddedLength deployment.length - deployment.length)
  | .enum shape => encodeWordBytesBE deployment.a ++ (if shape.dynamic then w 64 else ByteArray.empty) ++
      EnumArgumentExecution.body shape (enumTransaction deployment)

def canonicalSize (parameters : Parameters) (deployment : Deployment) : Nat :=
  (canonicalBytes parameters deployment).size

def chosen (shape : Shape) (deployment : Deployment) : Constructor :=
  EnumArgumentExecution.constructorAt shape deployment.choice

/-- Whether the arguments carry a `bytes` length Word: the parameter, or the
chosen constructor of an enum. -/
def carriesBytes (parameters : Parameters) (deployment : Deployment) : Bool :=
  match parameters with
  | .bytes => true
  | .enum shape => (chosen shape deployment).payload == .bytes
  | _ => false

/-- The position of the `bytes` length Word. -/
def lengthPosition (parameters : Parameters) : Nat :=
  match parameters with
  | .enum shape => bodyStart shape + shape.bodyHead
  | _ => 64

/-- The chosen constructor's head, after which a static enum's padding is
cut. -/
def narrowedSize (shape : Shape) (deployment : Deployment) : Nat :=
  64 + EnumArgument.headSize (chosen shape deployment).payload

/-- The argument bytes the deployment sends. -/
def argumentBytes (parameters : Parameters) (deployment : Deployment) : ByteArray :=
  let canonical := canonicalBytes parameters deployment
  let start := match parameters with
    | .enum shape => bodyStart shape
    | _ => 32
  let change : StdCalldata.Change := match deployment.malformation with
    | .none => .none
    | .truncate kept => .truncate kept
    | .trailing count pattern => .trailing count pattern
    | .offset value => .word 32 value
    | .length value => .word (lengthPosition parameters) value
    | .tag value => .word start value
    | .tagCut value => .word start value
    | .tail value => .word (start + 32) value
    | .narrow => match parameters with
        | .enum shape => .truncate (narrowedSize shape deployment)
        | _ => .none
  let changed := change.apply canonical
  match deployment.malformation with
  | .tagCut _ => changed.extract 0 (start + 32)
  | _ => changed

/-- A malformation within its bounds, where it applies: cuts inside the
arguments, the trailing bounds, the offset Word of a `bytes` value or a dynamic
enum, the length Word of a `bytes` value, unknown tags of an enum, the tail
offset of a dynamic enum's `bytes` constructor, and a static enum's narrower
constructor. -/
def Malformation.valid (parameters : Parameters) (deployment : Deployment) : Malformation → Bool
  | .none => true
  | .truncate kept => kept < canonicalSize parameters deployment
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .offset value => parameters.hasOffset && value.val != 64
  | .length value => carriesBytes parameters deployment && value.val != deployment.length
  | .tag value | .tagCut value => match parameters with
      | .enum shape => !shape.constructors.any (EnumArgument.tag · == value)
      | _ => false
  | .tail value => match parameters with
      | .enum shape => shape.dynamic && carriesBytes parameters deployment && value.val != shape.bodyHead
      | _ => false
  | .narrow => match parameters with
      | .enum shape => !shape.dynamic && narrowedSize shape deployment < canonicalSize parameters deployment
      | _ => false

/-- The record the constructor writes to slots 1 to 5. -/
structure Record where
  words : Word × Word × Word × Word × Word
  deriving BEq, Repr

def Record.toList (record : Record) : List Word :=
  let (d1, d2, d3, d4, d5) := record.words
  [d1, d2, d3, d4, d5]

/-- The revert data of a std rejection, or the decoded record. -/
abbrev Decision := Except ByteArray Record

private def selectorBytes (selector : Nat) : ByteArray :=
  ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8]

private def wordAt (input : ByteArray) (offset : Nat) : Word := Word.ofNatModulo (StdCalldata.wordAt input offset)

/-- The payload's zero-padded Word at `offset`, from the bytes that exist, as
std's copy leaves it in memory. -/
private def chunkAt (input : ByteArray) (start length offset : Nat) : Word :=
  let bytes := (input.extract (start + offset) (start + length)).extract 0 32
  Word.ofNatModulo ((bytes.data.toList ++ List.replicate (32 - bytes.size) (0 : UInt8)).foldl
    (fun total byte => total * 256 + byte.toNat) 0)

/-- A `bytes` value whose tail offset Word lies at `head` relative to `base`:
the offset `t <= size - base`, a length Word at `base + t` and a length that
fits after it. Returns the length and its two zero-padded chunks. -/
private def bytesAt (input : ByteArray) (base head : Nat) : Option (Word × Word × Word) :=
  let size := input.size
  if size - base < head + 32 then none
  else
    let tail := StdCalldata.wordAt input (base + head)
    if tail > size - base then none
    else if size - (base + tail) < 32 then none
    else
      let length := StdCalldata.wordAt input (base + tail)
      if length > size - (base + tail + 32) then none
      else
        let data := base + tail + 32
        some (Word.ofNatModulo length, if length > 0 then chunkAt input data length 0 else Word.zero,
          if length > 32 then chunkAt input data length 32 else Word.zero)

/-- An enum value's body at `start`: the tag compared with each constructor's
tag in declaration order before any field is read, then the chosen
constructor's fields, each Word required to exist. -/
private def enumAt (shape : Shape) (input : ByteArray) (start : Nat) : Except ByteArray (Nat × Word × Word × Word) :=
  let size := input.size
  let trunc : Except ByteArray (Nat × Word × Word × Word) := .error (selectorBytes truncatedError)
  if size - start < 32 then trunc
  else
    let found := wordAt input start
    match (shape.constructors.zipIdx.find? fun (constructor, _) => EnumArgument.tag constructor == found) with
    | none => .error ByteArray.empty
    | some (constructor, index) =>
        match constructor.payload with
        | .noWords => pure (index + 1, Word.zero, Word.zero, Word.zero)
        | .oneWord => if size - start < 64 then trunc else pure (index + 1, wordAt input (start + 32), Word.zero, Word.zero)
        | .twoWords | .pair =>
            if size - start < 96 then trunc
            else pure (index + 1, wordAt input (start + 32), wordAt input (start + 64), Word.zero)
        | .bytes => match bytesAt input start 32 with
            | some (length, first, second) => pure (index + 1, length, first, second)
            | none => trunc

/-- The pinned std's decision on the argument bytes, written from the
compiler's generated copy, `MemoryWordReader` and the derived decoders: `a`
first, then the parameters' values, every check comparing before it adds, as
std's do not wrap. A failure is `0x08638556`, an unknown tag empty data. -/
def stdDecide (parameters : Parameters) (input : ByteArray) : Decision := do
  let size := input.size
  let trunc : Decision := .error (selectorBytes truncatedError)
  let record := fun (d1 d2 d3 d4 d5 : Word) => (pure ⟨(d1, d2, d3, d4, d5)⟩ : Decision)
  match parameters with
  | .none => record (Word.ofNatModulo 1) Word.zero Word.zero Word.zero Word.zero
  | .word => if size < 32 then trunc else record (wordAt input 0) Word.zero Word.zero Word.zero Word.zero
  | .words => if size < 64 then trunc else record (wordAt input 0) (wordAt input 32) Word.zero Word.zero Word.zero
  | .bytes =>
      if size < 32 then trunc
      else match bytesAt input 0 32 with
        | some (length, first, second) => record (wordAt input 0) length first second Word.zero
        | none => trunc
  | .enum shape =>
      if size < 32 then trunc
      else
        let start? : Option Nat :=
          if shape.dynamic then
            if size < 64 then none
            else
              let offset := StdCalldata.wordAt input 32
              if offset > size then none else some offset
          else some 32
        match start? with
        | none => trunc
        | some start =>
            match enumAt shape input start with
            | .error data => .error data
            | .ok (index, w0, w1, w2) => record (wordAt input 0) (Word.ofNatModulo index) w0 w1 w2

/-- std's revert data for a rejected deployment, or none when it deploys. -/
def stdRejection? (parameters : Parameters) (deployment : Deployment) : Option ByteArray :=
  match stdDecide parameters (argumentBytes parameters deployment) with
  | .error data => some data
  | .ok _ => none

def arguments (parameters : Parameters) (deployment : Deployment) : String :=
  encodeBytesText (argumentBytes parameters deployment)

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- Slot zero holds the accumulator and slots one to five the record. -/
def observedSlots : List Word := (List.range ConstructorArguments.slotCount).map Word.ofNatModulo

def slotsJson : Json := toJson (observedSlots.map fun slot => toString slot.val)

def storageJson (account : Account) : Json := toJson (observedSlots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account
  | none => storageJson Account.empty

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- One top-level invocation of `contract` at the bound address over `world`:
none when the code does not resolve, `some none` when fuel runs out, and
otherwise the outcome and the final world. -/
private def invoke (contract : CheckedCoreContract) (world : WorldState) (bindings : Bindings)
    (input : HostStorageDriver.InputData) (fuel : Nat) : Option (Option (FrameOutcome Word × WorldState)) :=
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  match registry.resolve? world bindings.address with
  | none => none
  | some ⟨resolved, installed⟩ =>
      match TopLevelExecution.run resolved
          { target := bindings.address, caller := bindings.caller, callValue := Word.zero, inputData := input }
          installed fuel with
      | .completed terminal => some (some (terminal.outcome, terminal.finalWorld))
      | .outOfFuel .. => some none

/-- Independent original-Core observation of the deployment phase, then of
the runtime transactions over the deployed world. -/
def observeContracts (initializer runtime : CheckedCoreContract) (argumentInput : ByteArray)
    (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let installed := StorageExecution.initialWorldForContract initializer bindings
  let mut world := installed
  let mut rows : Array Json := #[]
  let mut stopped : Option String := some "deployment"
  let mut deployment : Json := Json.null
  if bounded : argumentInput.size < wordModulus then
    match invoke initializer installed bindings ⟨argumentInput, bounded⟩ fuel with
    | none => deployment := Json.mkObj [("status", toJson "resolution-failure")]
    | some none => deployment := Json.mkObj [("status", toJson "out-of-fuel")]
    | some (some (outcome, final)) =>
        world := final
        match outcome, final.account? bindings.address with
        | .returned _, some account =>
            world := final.putAccount bindings.address (account.withCode runtime.code)
            stopped := none
        | _, _ => pure ()
        deployment := Json.mkObj (outcomeFields outcome)
  else
    deployment := Json.mkObj [("status", toJson "input-limit")]
  deployment := deployment.setObjVal! "committedStorage" (worldStorage world bindings)
    |>.setObjVal! "accountStorage" (AccountStorage.contractJson world bindings.address)
  let initial := worldStorage world bindings
  let initialWhole := AccountStorage.contractJson world bindings.address
  if stopped.isNone then
    for (transaction, index) in transactions.zipIdx do
      if stopped.isNone then
        let prior := world
        let common := [("id", toJson transaction.id), ("index", toJson index)]
        match invoke runtime prior bindings (inputData transaction.flags transaction.input) fuel with
        | none =>
            rows := rows.push (Json.mkObj (common ++ [
              ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
              ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
            stopped := some transaction.id
        | some none =>
            rows := rows.push (Json.mkObj (common ++ [
              ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings),
              ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
            stopped := some transaction.id
        | some (some (outcome, final)) =>
            world := final
            rows := rows.push (Json.mkObj (common ++ outcomeFields outcome ++ [
              ("committedStorage", worldStorage world bindings),
              ("accountStorage", AccountStorage.contractJson world bindings.address)]))
  let deployed := (deployment.getObjValAs? String "status").toOption == some "returned"
  let complete := (deployed && stopped.isNone) ||
    (!deployed && (deployment.getObjValAs? String "status").toOption == some "reverted" && transactions.isEmpty)
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson), ("deployment", deployment),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if complete then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (deployment : Deployment) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContracts plan.initializer plan.runtime (argumentBytes plan.parameters deployment) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled row: whether it reverts, its whole output (std's revert data
for a rejected deployment, the one returned or reverted Word otherwise) and
slots zero to five. -/
structure ModelRow where
  reverted : Bool
  output : ByteArray
  slots : List Word

/-- The modelled deployment and transaction rows. The deployment follows
std's decision on the argument bytes and the constructor's writes; each
transaction follows the source: `sc_result = sc_step(sload(0) + input +
sload(1) + ... + sload(5))`, the write of slot zero, then the odd-flags revert,
which keeps the prior slots. A rejected deployment ends the rows. -/
def model (step : Aggregates.CheckedDAG) (fuel : Nat) (parameters : Parameters) (deployment : Deployment)
    (transactions : List Transaction) : Option (ModelRow × List ModelRow) := Id.run do
  match stdDecide parameters (argumentBytes parameters deployment) with
  | .error data =>
      return some (⟨true, data, List.replicate ConstructorArguments.slotCount Word.zero⟩, [])
  | .ok record =>
      let mut slots : List Word := Word.zero :: record.toList
      let deployed : ModelRow := ⟨false, encodeWordBytesBE Word.zero, slots⟩
      let mut rows : Array ModelRow := #[]
      for transaction in transactions do
        let total := slots.foldl (· + ·) Word.zero + transaction.input
        match stepResult step fuel total with
        | none => return none
        | some result =>
            if transaction.flags.val % 2 == 1 then
              rows := rows.push ⟨true, encodeWordBytesBE result, slots⟩
            else
              slots := slots.set 0 result
              rows := rows.push ⟨false, encodeWordBytesBE result, slots⟩
      return some (deployed, rows.toList)

end Solcore.Synthesis.Stateful.ConstructorArgumentsExecution
