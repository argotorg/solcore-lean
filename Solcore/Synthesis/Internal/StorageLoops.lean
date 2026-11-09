import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Internal.AdtStorage
import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Synthesis.Stateful.Sequence

/-!
# Profiles: storage and Keccak loops

The profiles `stateful-storage-loops` and `stateful-keccak-loops`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.KeccakLoop
/-! A checked protocol of a bounded loop over Keccak-addressed mapping entries
with one log per iteration. The ABI supplies `run(uint256 flags, uint256
input)`; the contract runs `input & mask` iterations of a closed aggregate
step. Iteration `i` uses the key `(input & ~7) | (i & keyMask)` and its entry
slot `keccak256(1 ++ key)`, the pinned std's layout for a mapping at base slot
one. It reads the entry and slot zero, writes `step(entry + slot 0 + input)` to
the entry and then to slot zero, and emits one log whose data is the written
value and whose topics are `i` and the key. Afterwards the result is slot zero
plus the iteration count, and the original flags parity selects return or
revert.

The hash closure is the mapping profile's, bound once. Logs use the event-log
profile's framing of Core's one word-log primitive: a header naming two topics
and one data Word, the data record, then the two topic records. The loop is
`mask` finite ordinal guards with literal ordinals and no counter cell; the
emitted source's while loop is a separate implementation. The public contract
runtime commits or rolls back the working world and journal together. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.KeccakLoop

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-keccak-loop-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The largest admitted loop mask, and so the most iterations a transaction runs. -/
def maxIterations : Nat := 7

/-- The accumulator field's slot and the mapping's base slot. -/
def accumulatorSlot : Nat := 0
def mappingSlot : Nat := Solcore.Synthesis.Core.StorageMapping.mappingSlot

/-- Each log has two topics, the ordinal and the key, and one data Word. -/
def logSite : Solcore.Synthesis.Core.EventLog.Site := {guard := 0, topics := 2, dataWords := 1}

/-- The bits of the input that keep their place in every key. -/
def highMask : Nat := 2 ^ 256 - 8

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index depth : Nat) (argument : Expr) : Expr := .apply (.var (index + depth)) argument
/-- The binder at `position`, counted from the outermost, in a frame of `depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (depth offset : Nat) : Expr := .caseE (host 8 depth (word offset)) (word 0) (.var 0)

/-- `let` each value in turn, then the body. -/
private def chain : List Expr → Expr → Expr
  | [], body => body
  | value :: rest, body => .letE value (chain rest body)

/-- Outer binders: the hash closure, the step, the flags, the input and the limit. -/
private def hashPosition : Nat := 0
private def stepPosition : Nat := 1
private def flagsPosition : Nat := 2
private def inputPosition : Nat := 3
private def limitPosition : Nat := 4
private def outerDepth : Nat := 5

/-- Iteration `ordinal` after the earlier iterations' Unit binders. Its own
binders are the key, the slot, the old entry, slot zero, the value, both writes
and the log frame's first three records; the frame's last record ends it. -/
private def iteration (keyMask ordinal : Nat) : Expr :=
  let d := outerDepth + ordinal
  let key := d
  let slot := d + 1
  let old := d + 2
  let accumulator := d + 3
  let value := d + 4
  .ifE (.binary .wordGt (bound d limitPosition) (word ordinal))
    (chain [
      .binary .wordOr (.binary .wordAnd (bound d inputPosition) (word highMask)) (word (ordinal &&& keyMask)),
      .apply (bound (d + 1) hashPosition) (.pair (word mappingSlot) (bound (d + 1) key)),
      host 0 (d + 2) (bound (d + 2) slot),
      host 0 (d + 3) (word accumulatorSlot),
      .apply (bound (d + 4) stepPosition)
        (.binary .wordAdd (.binary .wordAdd (bound (d + 4) old) (bound (d + 4) accumulator)) (bound (d + 4) inputPosition)),
      host 1 (d + 5) (.pair (bound (d + 5) slot) (bound (d + 5) value)),
      host 1 (d + 6) (.pair (word accumulatorSlot) (bound (d + 6) value)),
      host 13 (d + 7) (.pair (word (Solcore.Synthesis.Core.EventLog.headerTag logSite)) (word 0)),
      host 13 (d + 8) (.pair (word (Solcore.Synthesis.Core.EventLog.dataTag 1)) (bound (d + 8) value)),
      host 13 (d + 9) (.pair (word (Solcore.Synthesis.Core.EventLog.topicTag 1)) (word ordinal))]
      (host 13 (d + 10) (.pair (word (Solcore.Synthesis.Core.EventLog.topicTag 2)) (bound (d + 10) key))))
    .unit

private def iterations (keyMask : Nat) : Nat → Nat → Expr → Expr
  | 0, _, rest => rest
  | remaining + 1, ordinal, rest => .letE (iteration keyMask ordinal) (iterations keyMask remaining (ordinal + 1) rest)

/-- After the guards: the result is slot zero plus the limit, which odd flags revert. -/
private def completion (mask : Nat) : Expr :=
  let d := outerDepth + mask
  .letE (.binary .wordAdd (host 0 d (word accumulatorSlot)) (bound d limitPosition))
    (.ifE (.binary .wordEq (.binary .wordAnd (bound (d + 1) flagsPosition) (word 1)) (word 1))
      (.inRight .word (.inLeft .word (.var 0)))
      (.inLeft (.sum .word .word) (.var 0)))

private def contractExpression (hash stepBody : Expr) (mask keyMask : Nat) : Expr :=
  .letE hash
    (.letE stepBody
      (.letE (readInput 2 4)
        (.letE (readInput 3 36)
          (.letE (.binary .wordAnd (bound 4 inputPosition) (word mask))
            (iterations keyMask mask 0 (completion mask))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression Solcore.Synthesis.Core.StorageMapping.hashClosure step.program.body mask keyMask
}

def canonicalNodes (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Nat :=
  programNodes (canonicalProgram step mask keyMask)

/-- The fixed Keccak closure, which lies outside a case's node budget. -/
abbrev hashNodes : Nat := Solcore.Synthesis.Core.StorageMapping.hashNodes

private def placeholderNodes (mask : Nat) : Nat :=
  let body := contractExpression Solcore.Synthesis.Core.StorageMapping.hashClosure (word 0) mask 0
  programNodes {resultType := resultType, dataDefinitions := [], body := body}

/-- Syntax-only measurement of the shell, the wrapper without the hash closure
and the guards, using a one-node placeholder step that is never admitted or
run, as the mapping profile measures its overhead. The shell lies inside a
case's node budget. -/
def shellNodes : Nat :=
  placeholderNodes 0 - programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0} - hashNodes

/-- The guards of `mask` iterations, which lie outside a case's node budget. -/
def guardNodes (mask : Nat) : Nat := placeholderNodes mask - placeholderNodes 0

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  keyMask : Nat
  allowed : AllowedMask mask
  allowedKey : AllowedMask keyMask
  checked : (canonicalProgram step mask keyMask).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask plan.keyMask

def ofParts? (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if allowedKey : AllowedMask keyMask then
      if checked : (canonicalProgram step mask keyMask).check = true then
        some ⟨step, mask, keyMask, allowed, allowedKey, checked⟩
      else none
    else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem mask_le (plan : CheckedPlan) : plan.mask ≤ maxIterations := by
  rcases plan.allowed with mask | mask | mask | mask <;> simp [mask, maxIterations]

end CheckedPlan
end Solcore.Synthesis.Core.KeccakLoop
end

section
-- leanmerge: from Solcore.Synthesis.Core.StorageLoop
/-! A checked protocol of a bounded loop over declared slots. The ABI supplies
`run(uint256 flags, uint256 input)`; the contract runs `input & mask`
iterations of a closed aggregate step. Iteration `i` reads slots 0, 1, `1 + i`
and `2 + i`, applies the step to their wrapping sum plus the input, and writes
the result to slot `2 + i` and then to slot zero. Afterwards slot one grows by
the iteration count, and the original flags parity selects return or revert of
slot zero plus slot one. The loop is `mask` finite ordinal guards with literal
slots and no counter cell; the emitted source's while loop and counter are a
separate implementation. The public contract runtime commits or rolls back the
resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageLoop

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-loop-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The largest admitted mask, and so the most iterations a transaction runs. -/
def maxIterations : Nat := 7

/-- Slot zero, slot one and one slot for each iteration. -/
def slotCount : Nat := 2 + maxIterations

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- Iteration `ordinal` in a frame of `4 + ordinal` binders: the earlier
guards' Unit binders, then the limit, input, flags and step at `ordinal` to
`ordinal + 3`. Its four reads bind slots 0, 1, `1 + ordinal` and
`2 + ordinal`; the step's result is written to slot `2 + ordinal`, then to
slot zero. -/
private def iteration (ordinal : Nat) : Expr :=
  let locals := 4 + ordinal
  .ifE (.binary .wordGt (.var ordinal) (word ordinal))
    (.letE (host 0 locals (word 0))
      (.letE (host 0 (locals + 1) (word 1))
        (.letE (host 0 (locals + 2) (word (1 + ordinal)))
          (.letE (host 0 (locals + 3) (word (2 + ordinal)))
            (.letE (.apply (.var (ordinal + 7))
                (.binary .wordAdd (.binary .wordAdd (.binary .wordAdd (.binary .wordAdd
                  (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var (ordinal + 5))))
              (.letE (host 1 (locals + 5) (.pair (word (2 + ordinal)) (.var 0)))
                (host 1 (locals + 6) (.pair (word 0) (.var 1)))))))))
    .unit

private def iterations : Nat → Nat → Expr → Expr
  | 0, _, rest => rest
  | remaining + 1, ordinal, rest => .letE (iteration ordinal) (iterations remaining (ordinal + 1) rest)

/-- After the guards, `4 + mask` binders: the limit is local `mask` and the
flags local `mask + 2`. Slot one grows by the limit; the result is slot zero
plus slot one, which odd flags revert. -/
private def completion (mask : Nat) : Expr :=
  let locals := 4 + mask
  .letE (.binary .wordAdd (host 0 locals (word 1)) (.var mask))
    (.letE (host 1 (locals + 1) (.pair (word 1) (.var 0)))
      (.letE (.binary .wordAdd (host 0 (locals + 2) (word 0)) (host 0 (locals + 2) (word 1)))
        (.ifE (.binary .wordEq (.binary .wordAnd (.var (mask + 5)) (word 1)) (word 1))
          (.inRight .word (.inLeft .word (.var 0)))
          (.inLeft (.sum .word .word) (.var 0)))))

private def contractExpression (stepBody : Expr) (mask : Nat) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (.binary .wordAnd (.var 0) (word mask))
          (iterations mask 0 (completion mask)))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask : Nat) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body mask
}

def canonicalNodes (step : Aggregates.CheckedDAG) (mask : Nat) : Nat :=
  programNodes (canonicalProgram step mask)

private def placeholderNodes (mask : Nat) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) mask}

/-- Syntax-only measurement of the shell, the wrapper without guards, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes : Nat :=
  placeholderNodes 0 - programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The guards of `mask` iterations, which lie outside a case's node budget. -/
def guardNodes (mask : Nat) : Nat := placeholderNodes mask - placeholderNodes 0

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  allowed : AllowedMask mask
  checked : (canonicalProgram step mask).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask

def ofParts? (step : Aggregates.CheckedDAG) (mask : Nat) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if checked : (canonicalProgram step mask).check = true then some ⟨step, mask, allowed, checked⟩ else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem mask_le (plan : CheckedPlan) : plan.mask ≤ maxIterations := by
  rcases plan.allowed with mask | mask | mask | mask <;> simp [mask, maxIterations]

end CheckedPlan
end Solcore.Synthesis.Core.StorageLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.KeccakLoopEmitter
/-! Emit the Keccak-loop protocol as an actual source while loop. The contract
declares an `acc` field at slot zero and an `entries: mapping(word => word)`
field at base slot one; the source never computes a slot itself, since
indexing `entries[k]` goes through the pinned std, which hashes the base slot
followed by the key. The counter, key and value locals are declared before the
loop and assigned inside it. A 64-byte log buffer is reserved from the
free-memory pointer before the loop, and every iteration stores its value
there and calls the pinned `std.opcodes` wrapper `log2` with the counter and
the key as topics. This implementation is separate from the finite ordinal
guards of the checked Core reference. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeccakLoop

open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-keccak-loops-v2"
def wrapperVersion : String := "solcore-word-keccak-loops-contract-v1"
def contractName : String := "SynthesizedKeccakLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedKeccakLoopsDeploy"]
def runtimePath : List String := ["SynthesizedKeccakLoopsDeploy", "SynthesizedKeccakLoops"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["mload", "mstore", "revert_", "log2 as sc_log2"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    acc: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_base: word = (sc_input & ~7);",
    "        let sc_counter: word = 0;",
    "        let sc_key: word = 0;",
    "        let sc_value: word = 0;",
    "        let sc_ptr: word = mload(64);",
    "        mstore(64, (sc_ptr + 64));",
    "        while (sc_limit > sc_counter) {",
    "            sc_key = (sc_base | (sc_counter & " ++ toString plan.keyMask ++ "));",
    "            sc_value = sc_step(((entries[sc_key] + acc) + sc_input));",
    "            entries[sc_key] = sc_value;",
    "            acc = sc_value;",
    "            mstore(sc_ptr, sc_value);",
    "            sc_log2(sc_ptr, 32, sc_counter, sc_key);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        let sc_result: word = (acc + sc_limit);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(sc_ptr, sc_result);",
    "            revert_(sc_ptr, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.KeccakLoop
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.KeccakLoopExecution
/-! Execute the original checked Keccak-loop contract over a persistent account
world. Each invocation starts a fresh Core heap and an empty journal; only the
public terminal `finalWorld` becomes the next transaction's world, and only its
committed journal is reported, decoded under the event-log framing. The
observed slots are slot zero and the entry slot of every key the scenario's
transactions address, derived with the separate `Solcore.Abi.V1.Keccak256`
rather than the Core builders the contract runs.

`model` is an independent reading of the emitted source: a counter runs a
while loop over a slot map, each key's slot is hashed with that separate
Keccak, every iteration appends one log, and a reverted transaction keeps the
prior slots and commits no log. It evaluates the step's Core alone at each
argument and shares nothing with the guarded contract but that step. Tests
compare the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.KeccakLoopExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)

def historySchema : String := "solcore-lean.keccak-loop-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
abbrev inputData := EventLogExecution.inputData

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- The iterations a transaction runs: its input's bits under the loop mask. -/
def iterations (mask : Nat) (input : Word) : Nat := (input.bitAnd (Word.ofNatModulo mask)).val

/-- The key of iteration `ordinal`: the input's high bits and the ordinal's bits
under the key mask. -/
def key (keyMask : Nat) (input : Word) (ordinal : Nat) : Word :=
  (input.bitAnd (Word.ofNatModulo KeccakLoop.highMask)).bitOr (Word.ofNatModulo (ordinal &&& keyMask))

/-- The keys a transaction's iterations use, in iteration order. -/
def keys (mask keyMask : Nat) (input : Word) : List Word :=
  (List.range (iterations mask input)).map (key keyMask input)

/-- The pinned std's slot of `entries[key]`, from the independent ABI Keccak. -/
abbrev entrySlot := StorageMappingExecution.entrySlot

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- Slot zero and every addressed entry slot, in increasing numeric order
without duplicates: the protocol's complete write set. -/
def observedSlots (mask keyMask : Nat) (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => (keys mask keyMask tx.input).map entrySlot).foldl
    (fun slots slot => insertSlot slot slots) [Word.ofNatModulo KeccakLoop.accumulatorSlot]

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation. The code registry is resolved again
against each current committed world, so persistence cannot install a different
contract or retain one invocation's local heap or journal. -/
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
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := bindings.caller,
        callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              match EventLogExecution.decodeJournal terminal.committedJournal.logList with
              | .ok events =>
                  rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                    ("committedStorage", worldStorage world bindings slots),
                    ("accountStorage", AccountStorage.contractJson world bindings.address),
                    ("logs", EventLogExecution.eventsJson events)]))
                  match terminal.outcome with
                  | .trapped _ => stopped := some transaction.id
                  | _ => pure ()
              | .error error =>
                  rows := rows.push (Json.mkObj (common ++ [
                    ("status", toJson "observer-error"), ("detail", toJson error),
                    ("committedStorage", worldStorage world bindings slots),
                    ("accountStorage", AccountStorage.contractJson world bindings.address), ("logs", Json.null)]))
                  stopped := some transaction.id
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"), ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address), ("logs", Json.null)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", KeyedStorageExecution.slotsJson slots),
    ("framing", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("initialLogs", toJson ([] : List Json)),
    ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction) (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract (observedSlots plan.mask plan.keyMask transactions) transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled log: the ordinal and key topics and the written value. -/
structure ModelLog where
  ordinal : Nat
  key : Word
  value : Word
  deriving BEq

/-- One modelled transaction: whether it reverts, its result Word, the slots it
leaves committed as `(slot, value)` pairs and the logs it commits. -/
structure ModelRow where
  reverted : Bool
  result : Word
  storage : List (Word × Word)
  logs : List ModelLog
  deriving BEq

private def lookup (storage : List (Word × Word)) (slot : Word) : Word :=
  ((storage.find? fun (candidate, _) => candidate == slot).map Prod.snd).getD Word.zero

private def update (storage : List (Word × Word)) (slot value : Word) : List (Word × Word) :=
  (slot, value) :: storage.filter fun (candidate, _) => candidate != slot

def modelTransaction (step : Aggregates.CheckedDAG) (fuel mask keyMask : Nat) (prior : List (Word × Word))
    (transaction : Transaction) : Option ModelRow := Id.run do
  let limit := iterations mask transaction.input
  let base := transaction.input.bitAnd (Word.ofNatModulo KeccakLoop.highMask)
  let accumulator := Word.ofNatModulo KeccakLoop.accumulatorSlot
  let mut storage := prior
  let mut logs : Array ModelLog := #[]
  let mut counter := 0
  let mut failed := false
  -- At most the largest mask's iterations; the guard keeps the loop structural.
  for _ in List.range KeccakLoop.maxIterations do
    if !failed && limit > counter then
      let current := base.bitOr (Word.ofNatModulo (counter &&& keyMask))
      let slot := entrySlot current
      match stepResult step fuel (lookup storage slot + lookup storage accumulator + transaction.input) with
      | some value =>
          storage := update (update storage slot value) accumulator value
          logs := logs.push ⟨counter, current, value⟩
          counter := counter + 1
      | none => failed := true
  if failed then return none
  let result := lookup storage accumulator + Word.ofNatModulo limit
  let reverted := transaction.flags.val % 2 == 1
  return some ⟨reverted, result, if reverted then prior else storage, if reverted then [] else logs.toList⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel mask keyMask : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut storage : List (Word × Word) := []
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel mask keyMask storage transaction with
    | some row =>
        rows := rows.push row
        storage := row.storage
    | none => return none
  return some rows.toList

/-- A modelled row's value at each observed slot. -/
def modelSlots (row : ModelRow) (slots : List Word) : List Word := slots.map (lookup row.storage)

end Solcore.Synthesis.Stateful.KeccakLoopExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.KeccakLoopCases
/-! Keccak-loop cases retain one original host-aware Core contract, its loop and
key masks and an ordered history of `(flags, input)` transactions. Each
transaction records the iterations its input runs under the loop mask, which
replay recomputes. The observed slots are derived from the masks and the
transactions and are part of the case, so a reduction that changes a key also
changes the committed observation it is compared on. Reductions remove
transactions, lower either mask, reduce the step and simplify flags and inputs.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeccakLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeccakLoop (CheckedPlan)
open Solcore.Synthesis.Stateful.KeccakLoopExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-keccak-loop-case.v1"
def planSchema : String := "solcore-lean.keccak-loop-plan.v1"
def profileVersion : String := "stateful-keccak-loops-v1/keccak-loop-sequence-seed-v2"
def templateVersion : String := "keccak-entries-log2-accumulator-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-keccak-loop-corpus.v1"

/-- Flags values and input high parts; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts may exceed the step budget by the Keccak closure and the loop's guards. -/
def maxProgramNodes : Nat :=
  512 + Solcore.Synthesis.Core.KeccakLoop.hashNodes +
    Solcore.Synthesis.Core.KeccakLoop.guardNodes Solcore.Synthesis.Core.KeccakLoop.maxIterations

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical Keccak-loop contract exceeds its case limit"
  else throw s!"Keccak-loop scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

/-- Slot zero and every entry slot the transactions address. -/
def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.KeccakLoopExecution.observedSlots scenario.plan.mask scenario.plan.keyMask
    scenario.transactions

def transactionJson (mask : Nat) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("iterations", toJson (Solcore.Synthesis.Stateful.KeccakLoopExecution.iterations mask tx.input)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.KeccakLoopExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (mask : Nat) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson mask))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

/-- Transactions are decoded against the plan's mask, which fixes each
transaction's recorded iteration count. -/
def decodeTransactions (mask : Nat) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input")⟩
    unless row == transactionJson mask transaction do
      throw "transaction differs from canonical ID, flags, input, iterations, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "Keccak-loop scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask), ("keyMask", toJson plan.keyMask)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported Keccak-loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let keyMask ← json.getObjValAs? Nat "keyMask"
  let some plan := CheckedPlan.ofParts? step mask keyMask |
    throw "Keccak-loop plan has an invalid mask or key mask or failed full host-Core admission"
  unless json == planJson plan do throw "Keccak-loop plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "Keccak-loop contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("keccakLoopPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.plan.mask scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", toJson Solcore.Synthesis.Core.EventLog.framingVersion),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic Keccak-loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "keccakLoopPlan")
  let transactions ← decodeTransactions plan.mask (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical Keccak-loop plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") ==
      Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots do
    throw "observed slots must be slot zero and every addressed entry slot"
  return scenario

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.KeccakLoopExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- An input with the bank Word's high bits and `low` as its three low bits. -/
def loopInput (high : Word) (low : Nat) : Word :=
  (high.bitAnd (Word.ofNatModulo (2 ^ 256 - 8))).bitOr (Word.ofNatModulo (low % 8))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three flags, three input high parts, three low parts, then the completion
pattern. Each choice uses the high half of one draw from a separate stream. The
stream starts at SplitMix64's finalizer of the seed xor its domain, so that
consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 8, 8, 8, 4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6b65636c6f6f7071))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 9 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index),
      loopInput (bank (3 + index)) (choices.getD (6 + index) 0)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- Separate the two mask streams from each other and from other uses of a case seed. -/
private def maskDomain : UInt64 := 0x6b65636c6f6f706d
private def keyMaskDomain : UInt64 := 0x6b65636c6f6f706b

/-- SplitMix64 hashes of the seed, so that consecutive seeds vary in their masks
independently of each other and of the step's helper count and template. -/
def maskFor (seed : Seed) : Nat :=
  [1, 3, 7].getD ((GeneratorV2.mix (seed.toUInt64 ^^^ maskDomain)).toNat % 3) 7

def keyMaskFor (seed : Seed) : Nat :=
  [0, 1, 3, 7].getD ((GeneratorV2.mix (seed.toUInt64 ^^^ keyMaskDomain)).toNat % 4) 7

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget; the Keccak closure and the mask's guards
lie outside it. The complete contract is remeasured as the final budget
authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.KeccakLoop.shellNodes < nodes do
    throw "node budget is too small for the Keccak-loop wrapper or exceeds 512"
  let mask := maskFor seed
  let keyMask := keyMaskFor seed
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.KeccakLoop.shellNodes) revision
  let some plan := CheckedPlan.ofParts? step mask keyMask | throw "generated Keccak-loop plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤
      nodes + Solcore.Synthesis.Core.KeccakLoop.hashNodes + Solcore.Synthesis.Core.KeccakLoop.guardNodes mask do
    throw "Keccak-loop contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "keccak-loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("mask", toJson mask), ("keyMask", toJson keyMask), ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "Keccak-loop history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "Keccak-loop history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "Keccak-loop history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "keccak-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the loop mask, the key mask, complete program
size/literals, then flags and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.mask < source.plan.mask ∨
    (candidate.plan.mask = source.plan.mask ∧
      (candidate.plan.keyMask < source.plan.keyMask ∨
      (candidate.plan.keyMask = source.plan.keyMask ∧
        ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
        (complexity candidate.program.body = complexity source.program.body ∧
          valueWeight candidate < valueWeight source)))))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (mask keyMask : Nat)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask keyMask
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- One-transaction removals, lower loop masks, lower key masks, step
reductions, then per transaction the flags' parity bit and the input without
its high bits. Candidates still need execution to establish that they
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mask := source.plan.mask
  let keyMask := source.plan.keyMask
  let mut raw : List (Aggregates.CheckedDAG × Nat × Nat × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, mask, keyMask,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for lower in [3, 1, 0] do
    if lower < mask then
      raw := raw ++ [(source.plan.step, lower, keyMask, source.transactions)]
  for lower in [3, 1, 0] do
    if lower < keyMask then
      raw := raw ++ [(source.plan.step, mask, lower, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, mask, keyMask, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, mask, keyMask, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, mask, keyMask, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo Solcore.Synthesis.Core.KeccakLoop.maxIterations)})]
  let mut seen : List String := []
  let mut result := []
  for (step, lower, lowerKey, transactions) in raw do
    if let some reduced := sealReduction source step lower lowerKey transactions then
      -- The plan, not the program: without guards the program omits the key mask.
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.plan.mask reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.plan.mask parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.KeccakLoop.version),
      ("framingVersion", Solcore.Synthesis.Core.EventLog.framingVersion), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from Keccak-loop plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from Keccak-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "keccak-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated Keccak-loop provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.plan.mask expected.transactions == transactionsJson admitted.plan.mask admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.mask (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.mask admitted.plan.keyMask admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported Keccak-loop case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.KeccakLoop
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageLoopEmitter
/-! Emit the storage-loop protocol as an actual source while loop. The counter,
slot and value locals are declared before the loop and assigned inside it, and
each iteration's slots are computed from the counter, so the slot written by
one iteration is read by the next through a different expression. This
implementation is separate from the finite ordinal guards with literal slots
of the checked Core reference. Memory at zero is touched only before the
terminal revert. No emitter proof covers this wrapper. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLoop

open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-loops-v2"
def wrapperVersion : String := "solcore-word-storage-loops-contract-v1"
def contractName : String := "SynthesizedStorageLoops"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedStorageLoopsDeploy"]
def runtimePath : List String := ["SynthesizedStorageLoopsDeploy", "SynthesizedStorageLoops"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_"]
      (plan.step.helpers ++ [plan.step.entry]), ""]
  for (body, index) in plan.step.helpers.zipIdx do
    let rendered ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 body
    let result ← AggregateRenderer.requireValue rendered
    let name := "sc_fn" ++ toString index
    lines := lines ++ ["function " ++ name ++ "(sc_arg: word) returns (word) {"] ++
      rendered.lines ++ ["    return " ++ result ++ ";", "}", ""]
    names := name :: names
  let entry ← AggregateRenderer.render names .word [.word "sc_arg"] 4 0 plan.step.entry
  let result ← AggregateRenderer.requireValue entry
  lines := lines ++ ["function sc_step(sc_arg: word) returns (word) {"] ++
    entry.lines ++ ["    return " ++ result ++ ";", "}", "",
    "contract " ++ contractName ++ " {",
    "    function " ++ methodName ++ "(flags: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_limit: word = (sc_input & " ++ toString plan.mask ++ ");",
    "        let sc_counter: word = 0;",
    "        let sc_slot: word = 0;",
    "        let sc_value: word = 0;",
    "        while (sc_limit > sc_counter) {",
    "            sc_slot = (sc_counter + 2);",
    "            sc_value = sc_step(((((sload(0) + sload(1)) + sload((sc_slot - 1))) + sload(sc_slot)) + sc_input));",
    "            sstore(sc_slot, sc_value);",
    "            sstore(0, sc_value);",
    "            sc_counter = (sc_counter + 1);",
    "        }",
    "        sstore(1, (sload(1) + sc_limit));",
    "        let sc_result: word = (sload(0) + sload(1));",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageLoop
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.StorageLoopExecution
/-! Execute the original checked storage-loop contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Calldata is the
selector of `run(uint256,uint256)` with the flags and input Words.
Observations report the nine declared slots and the contract's whole committed
storage.

`model` is an independent reading of the emitted source: a counter runs a
while loop over a slot map, the slots are computed from the counter, and
reverted transactions keep the prior slots. It evaluates the step's Core alone
at each argument and shares nothing with the guarded contract but that step.
Tests compare the two; neither is an oracle for the differential paths. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageLoopExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)

def historySchema : String := "solcore-lean.storage-loop-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, then the flags and input Words. -/
def inputData (flags input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE flags ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags input : Word) : String := encodeBytesText (inputData flags input).bytes

/-- The iterations a transaction runs: its input's bits under the mask. -/
def iterations (mask : Nat) (input : Word) : Nat := (input.bitAnd (Word.ofNatModulo mask)).val

/-- Slot zero holds the accumulator, slot one the committed iteration total and
slot `2 + i` iteration `i`'s result. -/
def observedSlots : List Word := (List.range StorageLoop.slotCount).map Word.ofNatModulo

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
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"), ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          let invocation : TopLevelInvocation := {
            target := bindings.address, caller := bindings.caller,
            callValue := Word.zero, inputData := inputData transaction.flags transaction.input }
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

/-- The step's own Core result at one argument. -/
def stepResult (step : Aggregates.CheckedDAG) (fuel : Nat) (argument : Word) : Option Word :=
  match (step.instantiate argument).toCore.runStateful fuel with
  | .done (.word value) _ => some value
  | _ => none

/-- One modelled transaction: whether it reverts, its result Word and the slots
it leaves committed. The loop follows the source: `sc_limit = input & mask`,
a counter from zero while `sc_limit > sc_counter`, `sc_slot = sc_counter + 2`. -/
structure ModelRow where
  reverted : Bool
  result : Word
  slots : List Word
  deriving BEq

private def slotAt (slots : List Word) (slot : Nat) : Word := slots.getD slot Word.zero

def modelTransaction (step : Aggregates.CheckedDAG) (fuel mask : Nat) (prior : List Word)
    (transaction : Transaction) : Option ModelRow := Id.run do
  let limit := iterations mask transaction.input
  let mut slots := prior
  let mut counter := 0
  let mut failed := false
  -- At most the mask's iterations; the guard keeps the loop structural.
  for _ in List.range StorageLoop.maxIterations do
    if !failed && limit > counter then
      let slot := counter + 2
      let argument := slotAt slots 0 + slotAt slots 1 + slotAt slots (slot - 1) + slotAt slots slot + transaction.input
      match stepResult step fuel argument with
      | some value =>
          slots := (slots.set slot value).set 0 value
          counter := counter + 1
      | none => failed := true
  if failed then return none
  slots := slots.set 1 (slotAt slots 1 + Word.ofNatModulo limit)
  let result := slotAt slots 0 + slotAt slots 1
  let reverted := transaction.flags.val % 2 == 1
  return some ⟨reverted, result, if reverted then prior else slots⟩

/-- The modelled rows of a whole sequence from empty storage. -/
def model (step : Aggregates.CheckedDAG) (fuel mask : Nat) (transactions : List Transaction) :
    Option (List ModelRow) := Id.run do
  let mut slots : List Word := List.replicate StorageLoop.slotCount Word.zero
  let mut rows : Array ModelRow := #[]
  for transaction in transactions do
    match modelTransaction step fuel mask slots transaction with
    | some row =>
        rows := rows.push row
        slots := row.slots
    | none => return none
  return some rows.toList

end Solcore.Synthesis.Stateful.StorageLoopExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageLoopCases
/-! Storage-loop cases retain one original host-aware Core contract, its loop
mask and an ordered history of `(flags, input)` transactions. Each transaction
records the iterations its input runs under the mask, which replay recomputes.
Reductions remove transactions, lower the mask, reduce the step and simplify
flags and inputs. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLoop
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageLoop (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageLoopExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-storage-loop-case.v1"
def planSchema : String := "solcore-lean.storage-loop-plan.v1"
def profileVersion : String := "stateful-storage-loops-v1/loop-sequence-seed-v2"
def templateVersion : String := "loop-slots-total-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-storage-loop-corpus.v1"

/-- Flags values and input high parts; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts may exceed the step budget by the loop's guards. -/
def maxProgramNodes : Nat := 512 + Solcore.Synthesis.Core.StorageLoop.guardNodes StorageLoop.maxIterations

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical storage-loop contract exceeds its case limit"
  else throw s!"storage-loop scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (mask : Nat) (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("input", toJson (toString tx.input.val)),
  ("iterations", toJson (Solcore.Synthesis.Stateful.StorageLoopExecution.iterations mask tx.input)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageLoopExecution.calldata tx.flags tx.input)),
  ("value", toJson "0")]

def transactionsJson (mask : Nat) (transactions : List Transaction) : Json :=
  toJson (transactions.map (transactionJson mask))

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

/-- Transactions are decoded against the plan's mask, which fixes each
transaction's recorded iteration count. -/
def decodeTransactions (mask : Nat) (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← word (← row.getObjValAs? String "input")⟩
    unless row == transactionJson mask transaction do
      throw "transaction differs from canonical ID, flags, input, iterations, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "storage-loop scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program),
  ("mask", toJson plan.mask)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported storage-loop plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let mask ← json.getObjValAs? Nat "mask"
  let some plan := CheckedPlan.ofParts? step mask |
    throw "storage-loop plan has an invalid mask or failed full host-Core admission"
  unless json == planJson plan do throw "storage-loop plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "storage-loop contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("storageLoopPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.plan.mask scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.StorageLoopExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageLoop.version),
      ("templateVersion", toJson templateVersion),
      ("stepProfileVersion", toJson Aggregate.profileVersion),
      ("stepFunctionVersion", toJson Aggregates.version),
      ("stepTemplateVersion", toJson Aggregate.templateVersion),
      ("generatorVersion", toJson revision.version),
      ("emitterVersion", toJson emitterVersion), ("wrapperVersion", toJson wrapperVersion),
      ("features", toJson scenario.plan.step.features)]),
    ("contract", contractJson emitted), ("executionFuel", toJson fuel)]

def emitCase (scenario : CheckedScenario) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let emitted ← (emit scenario.plan).mapError reprStr
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic storage-loop case schema"
  let plan ← checkedPlan (← json.getObjVal? "storageLoopPlan")
  let transactions ← decodeTransactions plan.mask (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical storage-loop plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.StorageLoopExecution.slotsJson do
    throw "observed slots must be zero through eight"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageLoopExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- An input with the bank Word's high bits and `low` as its three low bits. -/
def loopInput (high : Word) (low : Nat) : Word :=
  (high.bitAnd (Word.ofNatModulo (2 ^ 256 - 8))).bitOr (Word.ofNatModulo (low % 8))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three flags, three input high parts, three low parts, then the completion
pattern. Each choice uses the high half of one draw from a separate stream. The
stream starts at SplitMix64's finalizer of the seed xor its domain, so that
consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := [6, 6, 6, 6, 6, 6, 8, 8, 8, 4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6c6f6f702d736571))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 9 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank index),
      loopInput (bank (3 + index)) (choices.getD (6 + index) 0)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- Separates the mask stream from other uses of a case seed. -/
private def maskDomain : UInt64 := 0x73746f726c6f6f70

/-- A SplitMix64 hash of the seed, so that consecutive seeds vary in their mask
independently of the step's helper count and template. -/
def maskFor (seed : Seed) : Nat :=
  [1, 3, 7].getD ((GeneratorV2.mix (seed.toUInt64 ^^^ maskDomain)).toNat % 3) 7

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The shell lies inside the budget; the mask's guards lie outside it. The
complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.StorageLoop.shellNodes < nodes do
    throw "node budget is too small for the storage-loop wrapper or exceeds 512"
  let mask := maskFor seed
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.StorageLoop.shellNodes) revision
  let some plan := CheckedPlan.ofParts? step mask | throw "generated storage-loop plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + Solcore.Synthesis.Core.StorageLoop.guardNodes mask do
    throw "storage-loop contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "storage-loop-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("mask", toJson mask), ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "storage-loop history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "storage-loop history did not follow its prescribed flags parities"

def generateCases (firstSeed : Seed) (nodes count attempts fuel : Nat)
    (revision : GeneratorRevision := .v1) (transactions : Nat := 3) : Json := Id.run do
  let mut cases : Array Json := #[]
  let mut excluded : Array Json := #[]
  let mut attempted := 0
  for index in List.range attempts do
    if cases.size < count then
      attempted := attempted + 1
      let seed := Seed.ofNat (firstSeed.toNat + index)
      let result := do
        unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
        let (scenario, origin) ← generatedScenario seed nodes revision transactions
        let emitted ← (emit scenario.plan).mapError reprStr
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "storage-loop history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "storage-loop-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.flags.val + transaction.input.val) 0

/-- Transaction count, the mask, complete program size/literals, then flags
and input values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (candidate.plan.mask < source.plan.mask ∨
    (candidate.plan.mask = source.plan.mask ∧
      ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
      (complexity candidate.program.body = complexity source.program.body ∧
        valueWeight candidate < valueWeight source)))))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG) (mask : Nat)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofParts? step mask
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- One-transaction removals, lower masks, step reductions, then per
transaction the flags' parity bit and the input without its high bits.
Candidates still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mask := source.plan.mask
  let mut raw : List (Aggregates.CheckedDAG × Nat × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step, mask,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for lower in [3, 1, 0] do
    if lower < mask then
      raw := raw ++ [(source.plan.step, lower, source.transactions)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, mask, source.transactions)]
  for index in List.range source.transactions.length do
    raw := raw ++ [(source.plan.step, mask, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(source.plan.step, mask, replaceAt source.transactions index fun tx =>
      {tx with input := tx.input.bitAnd (Word.ofNatModulo StorageLoop.maxIterations)})]
  let mut seen : List String := []
  let mut result := []
  for (step, lower, transactions) in raw do
    if let some reduced := sealReduction source step lower transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.plan.mask reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

private def reducedOrigin (parent : CheckedScenario) : Json := Json.mkObj [
  ("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
  ("parentProgram", Wire.encodeProgram parent.program),
  ("parentTransactions", transactionsJson parent.plan.mask parent.transactions)]

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.StorageLoop.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from storage-loop plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from storage-loop wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "storage-loop-generated" then
    let seedText ← origin.getObjValAs? String "seed"
    unless seedText.length ≤ 20 do throw "invalid saved seed"
    let some seed := seedText.toNat? | throw "invalid saved seed"
    unless seed < 2 ^ 64 && toString seed = seedText do throw "noncanonical saved seed"
    unless mask == revision.caseMask (Seed.ofNat seed) do throw "saved swarm mask differs from its generation seed"
    let (expected, expectedOrigin) ← generatedScenario (Seed.ofNat seed) (← origin.getObjValAs? Nat "maxProgramNodes") revision
      (← Stateful.Sequence.savedCount origin)
    let validationFuel ← origin.getObjValAs? Nat "validationFuel"
    unless validationFuel ≤ 10000000 do throw "saved validation fuel exceeds limit"
    unless origin == expectedOrigin.setObjVal! "validationFuel" (toJson validationFuel) do
      throw "saved origin differs from generated storage-loop provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.plan.mask expected.transactions == transactionsJson admitted.plan.mask admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions parentPlan.mask (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.plan.mask admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == reducedOrigin parent do throw "noncanonical reduced origin"
  else throw "unsupported storage-loop case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced =>
    emitCase reduced.candidate (reducedOrigin source) fuel revision mask
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageLoop
end
