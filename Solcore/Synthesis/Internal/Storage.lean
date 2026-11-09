import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Core.Wire.Conversions
import Solcore.Frontend.RustHull.Precompiles
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Lean.Data.Json
import Solcore.Synthesis.Stateful.Sequence
import Solcore.Abi.Keccak256

/-!
# Profiles: storage

The profiles `stateful-storage`, `stateful-storage-rollback`, `stateful-keyed-storage`,
`stateful-mapping` and `stateful-ledger`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.KeyedStorage
/-! A checked keyed-storage protocol around a closed aggregate step. The ABI
supplies a full-width slot key and an input Word. The contract writes the key
slot, its wrapping successor and the fixed counter slot zero in that order, so
keys zero and maximum alias the counter. All three slots are reread before the
original input parity selects return or revert. The public contract runtime
commits or rolls back the resulting working world; the Core expression itself
does not restore storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.KeyedStorage

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-keyed-storage-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The fixed counter slot. Keys zero and maximum alias it directly and through
the wrapping successor write respectively. -/
def counterSlot : Nat := 0

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- After the result binding, the original input is local ten; the three Unit
write binders and three final reads remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- Every host application names its exact local depth. Writes occur in the
order key, key + 1, counter; the later write wins when slots alias. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (.var 1))
          (.letE (host 0 4 (word counterSlot))
            (.letE (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1)))
              (.letE (host 1 6 (.pair (.var 4) (.var 0)))
                (.letE (host 1 7 (.pair (.binary .wordAdd (.var 5) (word 1)) (.var 3)))
                  (.letE (host 1 8 (.pair (word counterSlot) (.binary .wordAdd (.var 3) (word 1))))
                    (.letE (host 0 9 (.var 7))
                      (.letE (host 0 10 (.binary .wordAdd (.var 8) (word 1)))
                        (.letE (host 0 11 (word counterSlot))
                          (.letE (.binary .wordAdd (.binary .wordAdd (.var 2) (.var 1)) (.var 0))
                            completion))))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead measurement; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

abbrev ofStep? := ofParts?

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

end CheckedPlan
end Solcore.Synthesis.Core.KeyedStorage
end

section
-- leanmerge: from Solcore.Synthesis.Core.StorageContract
/-! A fixed two-slot storage protocol around a checked, closed aggregate DAG.
Only storageRead, storageWrite and inputDataWordBE? from the Wire host table are
used by this wrapper. Differential cases supply exactly the run(uint256)
selector and one ABI Word; malformed calldata behavior is outside this profile.
The original Core entry closure is bound once for each contract invocation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageContract

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-contract-v1"

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- Fixed host indices are offset by the complete current local prefix,
including both Unit sequencing binders after the storage writes. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (word 4)) (word 0) (.var 0))
      (.letE (.apply (.var 2) (word 0))
        (.letE (.apply (.var 3) (word 1))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (word 0) (.var 0)))
              (.letE (.apply (.var 7) (.pair (word 1) (.binary .wordAdd (.var 2) (word 1))))
                (.binary .wordAdd (.apply (.var 7) (word 0)) (.apply (.var 7) (word 1)))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := .word
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Measured wrapper overhead, using a one-node expression only to count syntax.
The placeholder is never admitted as contract code or executed. -/
def programOverhead : Nat :=
  programNodes {resultType := .word, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

abbrev ofStep? := ofParts?

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

def wordCode (plan : CheckedPlan) : CheckedHostCoreWordProgram := ⟨plan.code, rfl⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.returnWord plan.wordCode

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.StorageContract
end

section
-- leanmerge: from Solcore.Synthesis.Core.StorageMapping
/-! A checked protocol over one Keccak-addressed storage mapping. The calldata
of `run(uint256 flags, uint256 key, uint256 input)` holds three Words. The
contract derives the entry slots `keccak256(1 ++ key)` and `keccak256(1 ++
(key + 1))`, the pinned std's layout for a mapping at base slot one. It writes
`step(input + old)` to the first, `old + 1` to the second and an incremented
counter to slot zero, rereads all three, and lets the original flags parity
select return or revert. The public contract runtime commits or rolls back the
resulting working world.

The hash closure absorbs the two big-endian Words as one Keccak block, a small
new piece of code, and then applies the Core Keccak-f[1600] permutation and
digest builders the Hull import path uses for its `keccak256` builtin. Those
builders are proved against the independent `KeccakSemantics` specification
(`KeccakPermutationCorrespondence.permute_evaluates` and
`KeccakAbsorptionCorrespondence.digest_evaluates`). -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageMapping

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Frontend.RustHull

def version : String := "core-keccak-mapping-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The counter field's slot and the mapping field's base slot. -/
def counterSlot : Nat := 0
def mappingSlot : Nat := 1

/-- Lane `chunk` of the 64-byte block `first ++ second`, where lanes zero to
three take the big-endian bytes of `first` and lanes four to seven those of
`second`, each lane little-endian as Keccak absorbs it. -/
def blockLane (word : Solcore.Core.Expr) (chunk : Nat) : Solcore.Core.Expr :=
  (List.range 8).foldl (fun lane index =>
    .binary .wordOr lane (Keccak.shift (.binary .wordByte (Keccak.number (8 * chunk + index)) word) (8 * index)))
    (Keccak.number 0)

/-- The absorbed state of one 136-byte rate block: the eight message lanes,
Ethereum's `0x01` domain byte at offset 64 and the final `0x80` at offset 135. -/
def absorbedBlock (first second : Solcore.Core.Expr) : Solcore.Core.Expr :=
  Keccak.packet ((List.range 25).map fun index =>
    if index < 4 then blockLane first index
    else if index < 8 then blockLane second (index - 4)
    else if index = 8 then Keccak.number 1
    else if index = 16 then Keccak.number (2 ^ 63)
    else Keccak.number 0)

/-- `fun (first, second) => keccak256(first ++ second)` in ordinary Core. -/
def coreHash : Solcore.Core.Expr :=
  .lambda (.product .word .word) .word
    (.letE (.first (.var 0))
      (.letE (.second (.var 1))
        (.letE (Keccak.permute (absorbedBlock (.var 1) (.var 0))) (Keccak.digest (.var 0)))))

/-- The same closure as a Wire expression. The conversion succeeds, which the
tests check; a failed conversion would leave an ill-typed `Unit` that full
admission rejects, never a different hash. -/
def hashClosure : Expr := (Expr.ofCore? coreHash).getD .unit

/-- The fixed Keccak closure's size, which lies outside the step's node budget. -/
def hashNodes : Nat :=
  programNodes {resultType := .function (.product .word .word) .word, dataDefinitions := [], body := hashClosure}

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- After the result binding, the flags are local nine; both entry slots, the
old entry, the key, the input, the step and the hash closure remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 9) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE hashClosure
    (.letE stepBody
      (.letE (readAt 2 (word 4))
        (.letE (readAt 3 (word 36))
          (.letE (readAt 4 (word 68))
            (.letE (.apply (.var 4) (.pair (word mappingSlot) (.var 1)))
              (.letE (.apply (.var 5) (.pair (word mappingSlot) (.binary .wordAdd (.var 2) (word 1))))
                (.letE (host 0 7 (.var 1))
                  (.letE (host 1 8 (.pair (.var 2) (.apply (.var 6) (.binary .wordAdd (.var 3) (.var 0)))))
                    (.letE (host 1 9 (.pair (.var 2) (.binary .wordAdd (.var 1) (word 1))))
                      (.letE (host 1 10 (.pair (word counterSlot)
                          (.binary .wordAdd (host 0 10 (word counterSlot)) (word 1))))
                        (.letE (.binary .wordAdd
                            (.binary .wordAdd (host 0 11 (.var 5)) (host 0 11 (.var 4)))
                            (host 0 11 (word counterSlot)))
                          completion)))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead of the protocol around the step, without the fixed
Keccak closure; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0} - hashNodes

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

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

end CheckedPlan
end Solcore.Synthesis.Core.StorageMapping
end

section
-- leanmerge: from Solcore.Synthesis.Core.StorageLedger
/-! A checked sender-keyed ledger over the Keccak-addressed mapping of
`StorageMapping`. The calldata of `run(uint256 flags, uint256 recipient,
uint256 amount, uint256 input)` holds four Words; the sender is the
invocation's caller, read with the `callerAddress` host request. The contract
credits `B = entries[sender] + step(input)` at `keccak256(1 ++ sender)`,
reverts with `B` when the amount exceeds it, and otherwise writes `B - amount`
to the sender's entry, adds the amount to the entry at `keccak256(1 ++
recipient)`, increments the counter at slot zero and rereads all three. The
original flags parity then selects return or revert. The public contract
runtime commits or rolls back the resulting working world.

Slots are hashed with the mapping profile's closure, built from the Core
Keccak-f[1600] permutation and digest builders the Hull import path uses for
its `keccak256` builtin and proved against the independent `KeccakSemantics`
specification. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageLedger

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-sender-ledger-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The counter field's slot and the mapping field's base slot, as for the mapping. -/
def counterSlot : Nat := StorageMapping.counterSlot
def mappingSlot : Nat := StorageMapping.mappingSlot

/-- The fixed Keccak closure's size, which lies outside the step's node budget. -/
def hashNodes : Nat := StorageMapping.hashNodes

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- After the result binding, the flags are local eleven; both entry slots, the
credited balance, the sender, the calldata Words, the step and the hash
closure remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 11) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- With the credited balance as local zero: write the sender's and the
recipient's entries, increment the counter, reread all three and complete. -/
private def transfer : Expr :=
  .letE (host 1 10 (.pair (.var 2) (.binary .wordSub (.var 0) (.var 5))))
    (.letE (host 1 11 (.pair (.var 2) (.binary .wordAdd (host 0 11 (.var 2)) (.var 6))))
      (.letE (host 1 12 (.pair (word counterSlot) (.binary .wordAdd (host 0 12 (word counterSlot)) (word 1))))
        (.letE (.binary .wordAdd
            (.binary .wordAdd (host 0 13 (.var 5)) (host 0 13 (.var 4)))
            (host 0 13 (word counterSlot)))
          completion)))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE StorageMapping.hashClosure
    (.letE stepBody
      (.letE (readAt 2 (word 4))
        (.letE (readAt 3 (word 36))
          (.letE (readAt 4 (word 68))
            (.letE (readAt 5 (word 100))
              (.letE (host 5 6 .unit)
                (.letE (.apply (.var 6) (.pair (word mappingSlot) (.var 0)))
                  (.letE (.apply (.var 7) (.pair (word mappingSlot) (.var 4)))
                    (.letE (.binary .wordAdd (host 0 9 (.var 1)) (.apply (.var 7) (.var 3)))
                      (.ifE (.binary .wordGt (.var 5) (.var 0))
                        (.inRight .word (.inLeft .word (.var 0)))
                        transfer))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead of the protocol around the step, without the fixed
Keccak closure; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0} - hashNodes

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

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

end CheckedPlan
end Solcore.Synthesis.Core.StorageLedger
end

section
-- leanmerge: from Solcore.Synthesis.Core.StorageRollback
/-! A checked two-slot protocol with a typed rollback outcome. Both writes and
the final reads run before the original ABI input selects return or revert.
The public contract runtime commits or rolls back the resulting working world;
the Core expression itself does not restore storage or simulate a transaction. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageRollback

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-rollback-contract-v1"

def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- After the result binding, the original input is at index six. The two Unit
write binders remain in scope. The captured result is the tentative slot sum. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 6) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (word 4)) (word 0) (.var 0))
      (.letE (.apply (.var 2) (word 0))
        (.letE (.apply (.var 3) (word 1))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (word 0) (.var 0)))
              (.letE (.apply (.var 7) (.pair (word 1) (.binary .wordAdd (.var 2) (word 1))))
                (.letE (.binary .wordAdd (.apply (.var 7) (word 0)) (.apply (.var 7) (word 1)))
                  completion)))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead measurement; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, checked⟩ else none

abbrev ofStep? := ofParts?

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

end CheckedPlan
end Solcore.Synthesis.Core.StorageRollback
end

section
-- leanmerge: from Solcore.Synthesis.Source.KeyedStorageEmitter
/-! Emit the fixed keyed-storage protocol. The ABI key selects a full-width
slot; the key slot, its wrapping successor and counter slot zero are written in
the same order as the original Core contract. Odd original inputs revert after
all writes and rereads with the tentative sum encoded as exactly 32 bytes; even
inputs return that Word through the ABI. Memory at zero is touched only before
the terminal revert. The arbitrary checked aggregate entry is preserved.
`ScalarMeaning.KeyedStorage.emit_source_meaning` relates the emitted text to the
original Core contract's top-level transaction, returned or reverted, for every
key under an independent keyed source semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeyedStorage

open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

def emitterVersion : String := "solcore-source-keyed-storage-v3"
def wrapperVersion : String := "solcore-word-keyed-storage-contract-v1"
def contractName : String := "SynthesizedKeyedStorage"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256)"
def selector : String := "0x7357f5d2"
def deployPath : List String := ["SynthesizedKeyedStorageDeploy"]
def runtimePath : List String := ["SynthesizedKeyedStorageDeploy", "SynthesizedKeyedStorage"]

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
    "    function " ++ methodName ++ "(key: uint256, input: uint256) public returns (uint256) {",
    "        let sc_key: word = Typedef.rep(key);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = sload(sc_key);",
    "        let sc_count: word = sload(0);",
    "        let sc_computed: word = sc_step(sc_input + sc_old);",
    "        sstore(sc_key, sc_computed);",
    "        sstore(sc_key + 1, sc_old);",
    "        sstore(0, sc_count + 1);",
    "        let sc_final_key: word = sload(sc_key);",
    "        let sc_final_next: word = sload(sc_key + 1);",
    "        let sc_final_count: word = sload(0);",
    "        let sc_result: word = sc_final_key + sc_final_next + sc_final_count;",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.KeyedStorage
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageEmitter
/-! Emit the fixed two-slot storage protocol with an arbitrary checked step
entry. ABI validation belongs to the case boundary; this profile claims no
correspondence for malformed calldata. `ScalarMeaning.Storage.emit_source_meaning`
relates the emitted text to the original Core contract's top-level transaction
under an independent storage source semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Storage

open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-v3"
def wrapperVersion : String := "solcore-word-storage-contract-v1"
def contractName : String := "SynthesizedStorage"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedStorageDeploy"]
def runtimePath : List String := ["SynthesizedStorageDeploy", "SynthesizedStorage"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore"]
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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old0: word = sload(0);",
    "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);",
    "        sstore(1, sc_old1 + 1);",
    "        let sc_final0: word = sload(0);",
    "        let sc_final1: word = sload(1);",
    "        return uint256(sc_final0 + sc_final1);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.Storage
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.StorageExecution
/-! Execute the original checked Core contract over a persistent account world.
Each invocation starts a fresh Core heap. Only the public terminal `finalWorld`
is passed to the next transaction; suspended working state is never committed.
Each observation reports slots zero and one and the contract's whole committed
storage, enumerated exactly from its account. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)

def historySchema : String := "solcore-lean.storage-history.v2"
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
  let initialWhole := AccountStorage.contractJson world bindings.address
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
            ("committedStorage", worldStorage prior bindings),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("initialStorage", initial), ("initialAccountStorage", initialWhole),
    ("transactions", .arr rows), ("finalStorage", worldStorage world bindings),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.StorageExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageCases
/-! A storage case retains one original host-aware Core contract and an ordered
transaction history. No saved output is an oracle: observation runs that contract
from an empty persistent world with the supplied execution bindings. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.Storage
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageContract (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-storage-case.v1"
def planSchema : String := "solcore-lean.storage-plan.v1"
def profileVersion : String := "stateful-storage-v2/sequence-seed-v2"
def templateVersion : String := "two-slot-feedback-v1"
def storageCorpusSchema : String := "solcore-lean.semantic-storage-corpus.v1"

def boundaryInputs : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 3, Word.ofNatModulo 7,
    Word.maximum, Word.ofNatModulo (2 ^ 255)]

def validId (id : String) : Bool :=
  !id.isEmpty && id.length ≤ 64 && id.toList.all (fun char =>
    char.isDigit || ('a' ≤ char && char ≤ 'z') || ('A' ≤ char && char ≤ 'Z') ||
    char == '_' || char == '-')

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => validId tx.id) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical storage contract exceeds the 512-node case limit"
  else throw s!"storage scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageExecution.calldata tx.input)), ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let id ← row.getObjValAs? String "id"
    let inputText ← row.getObjValAs? String "input"
    unless inputText.length ≤ 78 do throw "transaction input exceeds a Word"
    let input ← Input.inputWord inputText
    let transaction : Transaction := ⟨id, input⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "storage scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported storage plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "storage contract failed full host-Core admission"
  unless json == planJson plan do throw "storage plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "storage contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]
def observedSlotsJson : Json := toJson (["0", "1"] : List String)

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("storagePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson StorageContract.version), ("templateVersion", toJson templateVersion),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic storage case schema"
  let plan ← checkedPlan (← json.getObjVal? "storagePlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical storage plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageExecution.observe scenario.plan scenario.transactions bindings fuel

/-- Three boundary-input indices, each the high half of one draw from a separate
stream. The stream starts at SplitMix64's finalizer of the seed xor its domain,
so that consecutive seeds' indices do not step by a fixed residue, and the
indices do not share the step seed's helper-count and template digits. -/
def sequenceIndices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x73746f72652d7371))
  let mut values : Array Nat := #[]
  for _ in List.range 3 do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % 6)
    state := next
  return values.toList

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  (sequenceIndices seed).zipIdx.map fun (inputIndex, index) =>
    ⟨"tx-" ++ toString (first + index), boundaryInputs[inputIndex]?.getD Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && StorageContract.programOverhead < nodes do
    throw "node budget is too small for the storage wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - StorageContract.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated storage plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "storage contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "storage-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceIndices", toJson (Stateful.Sequence.blocks (fun blockSeed _ => sequenceIndices blockSeed) seed
      transactions))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "storage history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.all (fun row => (row.getObjValAs? String "status").toOption == some "returned") do
    throw "storage history did not return from every transaction"

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
            error == "storage history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "storage-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson storageCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime inputs.
Every axis is a natural number and the comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      inputWeight candidate < inputWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let key := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", StorageContract.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from storage plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from storage wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "storage-generated" then
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
      throw "saved origin differs from generated storage provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported storage case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson storageCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.Storage
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.KeyedStorageExecution
/-! Execute the original checked keyed-storage contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Observations report
exactly the declared slots: the counter and every transaction key and wrapping
successor. Each observation also reports the contract's whole committed
storage, enumerated exactly from its account. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.KeyedStorageExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)

def historySchema : String := "solcore-lean.keyed-storage-history.v2"

/-- One caller and one installed contract, exactly as for the two-slot profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  key : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256)`, followed by the key and the input
as two big-endian Words. Malformed calldata is outside this profile. -/
def inputData (key input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x73, 0x57, 0xf5, 0xd2] ++ encodeWordBytesBE key ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (key input : Word) : String := encodeBytesText (inputData key input).bytes

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The protocol's complete write set: the counter, each key and each key's
wrapping successor, in increasing numeric order without duplicates. -/
def observedSlots (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => [tx.key, tx.key.add (Word.ofNatModulo 1)]).foldl
    (fun slots slot => insertSlot slot slots)
    [Word.ofNatModulo Solcore.Synthesis.Core.KeyedStorage.counterSlot]

def slotsJson (slots : List Word) : Json := toJson (slots.map fun slot => toString slot.val)

def storageJson (account : Account) (slots : List Word) : Json := toJson (slots.map fun slot => Json.mkObj [
  ("slot", toJson (toString slot.val)),
  ("value", toJson (toString (account.storageRead slot).val))])

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => storageJson account slots
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
  let slots := observedSlots transactions
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
        callValue := Word.zero, inputData := inputData transaction.key transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings slots),
                ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
              stopped := some transaction.id
  return Json.mkObj [
    ("schema", toJson historySchema), ("bindings", StorageExecution.bindingsJson bindings),
    ("fuelPerTransaction", toJson fuel), ("observedSlots", slotsJson slots),
    ("initialStorage", initial), ("initialAccountStorage", initialWhole), ("transactions", .arr rows),
    ("finalStorage", worldStorage world bindings slots),
    ("finalAccountStorage", AccountStorage.contractJson world bindings.address),
    ("status", toJson (if stopped.isNone then "complete" else "incomplete")),
    ("stoppedAt", stopped.map toJson |>.getD Json.null),
    ("unexecuted", toJson ((transactions.drop rows.size).map (·.id)))]

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.KeyedStorageExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.KeyedStorageCases
/-! Keyed-storage cases retain one original host-aware Core contract and an
ordered history of `(key, input)` transactions. The observed slots are derived
from that history and are part of the case, so a reduction that changes a key
also changes the committed observation it is compared on. Saved outputs are
never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.KeyedStorage
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.KeyedStorage (CheckedPlan)
open Solcore.Synthesis.Stateful.KeyedStorageExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-keyed-storage-case.v1"
def planSchema : String := "solcore-lean.keyed-storage-plan.v1"
def profileVersion : String := "stateful-keyed-storage-v2/keyed-sequence-seed-v2"
def templateVersion : String := "keyed-slot-successor-counter-revert-odd-v1"
def keyedCorpusSchema : String := "solcore-lean.semantic-keyed-storage-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Keys zero and maximum alias the counter; zero/one and maximum-minus-one/
maximum alias each other's successor slots; the remaining keys are full-width. -/
def keyBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo (2 ^ 255),
    Word.ofNatModulo 0x0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef,
    Word.ofNatModulo (2 ^ 256 - 2), Word.maximum]

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
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.observedSlots scenario.transactions

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical keyed-storage contract exceeds the 512-node case limit"
  else throw s!"keyed-storage scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("key", toJson (toString tx.key.val)), ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.KeyedStorageExecution.calldata tx.key tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "key", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, key, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "keyed-storage scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported keyed-storage plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "keyed-storage contract failed full host-Core admission"
  unless json == planJson plan do throw "keyed-storage plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "keyed-storage contract exceeds the 512-node case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson (scenario : CheckedScenario) : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("keyedStoragePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson scenario),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.KeyedStorage.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic keyed-storage case schema"
  let plan ← checkedPlan (← json.getObjVal? "keyedStoragePlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical keyed-storage plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson scenario do
    throw "observed slots must be the counter and every transaction key and successor"
  return scenario

def aliasCatalog : List String := ["key-counter", "successor-counter", "repeated-key", "successor-key"]

/-- Static slot aliasing among the transaction keys, in catalog order. This is
syntax of the sequence; it does not claim that an aliasing write committed. -/
def aliases (transactions : List Transaction) : List String :=
  let keys := transactions.map (·.key)
  let counter := Word.ofNatModulo Solcore.Synthesis.Core.KeyedStorage.counterSlot
  let successor := fun (key : Word) => key.add (Word.ofNatModulo 1)
  aliasCatalog.filter fun kind =>
    if kind = "key-counter" then keys.contains counter
    else if kind = "successor-counter" then keys.any (successor · == counter)
    else if kind = "repeated-key" then keys.eraseDups.length < keys.length
    else (keys.zipIdx.any fun (left, i) => keys.zipIdx.any fun (right, j) => i != j && successor left == right)

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- A separate stream keeps sequence choices independent of the step seed's
helper-count and template digits. Each choice uses the high half of one draw:
the low bits of a power-of-two LCG have short periods. The stream starts at
SplitMix64's finalizer of the seed xor its domain, so that consecutive seeds'
choices do not step by a fixed residue. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6b657965642d7378))
  let mut values : Array Nat := #[]
  for bound in [6, 6, 6, 6, 6, 6, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), keyBank.getD (choices.getD index 0) Word.zero,
      parityInput odd (boundaryInputs.getD (choices.getD (3 + index) 0) Word.zero)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.KeyedStorage.programOverhead < nodes do
    throw "node budget is too small for the keyed-storage wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.KeyedStorage.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated keyed-storage plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "keyed-storage contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "keyed-storage-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "keyed-storage history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.input.val % 2 == 1))) do
    throw "keyed-storage history did not follow its prescribed input parities"

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
            error == "keyed-storage history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "keyed-storage-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson keyedCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Keys and inputs both contribute; a key reduction can remove aliasing. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.key.val + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime keys and
inputs. Every axis is a natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      valueWeight candidate < valueWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

/-- Step reductions, then per-transaction removal and bank replacements of the
input and the key. Candidates still need execution to preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
    for key in keyBank do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with key := key} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.KeyedStorage.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from keyed-storage plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from keyed-storage wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "keyed-storage-generated" then
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
      throw "saved origin differs from generated keyed-storage provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported keyed-storage case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson keyedCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.KeyedStorage
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageLedgerEmitter
/-! Emit the fixed sender-keyed ledger protocol. The contract declares the
mapping profile's `counter` field at slot zero and `entries: mapping(word =>
word)` field at base slot one, reads the sender with `caller()` from
`std.opcodes` and never computes a slot itself: indexing goes through the
pinned std, which hashes the base slot followed by the key. The credit, the
insufficient-balance revert, the two entry writes, the counter update, the
rereads and the odd-flags revert follow the original Core contract in order.
Memory at zero is touched only before a terminal revert, after the std's own
hashing scratch use. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLedger

open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)

def emitterVersion : String := "solcore-source-sender-ledger-v2"
def wrapperVersion : String := "solcore-word-sender-ledger-contract-v1"
def contractName : String := "SynthesizedLedger"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256,uint256)"
def selector : String := "0x15509d2b"
def deployPath : List String := ["SynthesizedLedgerDeploy"]
def runtimePath : List String := ["SynthesizedLedgerDeploy", "SynthesizedLedger"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["caller", "mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    counter: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++
      "(flags: uint256, recipient: uint256, amount: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_recipient: word = Typedef.rep(recipient);",
    "        let sc_amount: word = Typedef.rep(amount);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_sender: word = caller();",
    "        let sc_balance: word = entries[sc_sender] + sc_step(sc_input);",
    "        if (sc_amount > sc_balance) {",
    "            mstore(0, sc_balance);",
    "            revert_(0, 32);",
    "        }",
    "        entries[sc_sender] = sc_balance - sc_amount;",
    "        entries[sc_recipient] = entries[sc_recipient] + sc_amount;",
    "        counter = counter + 1;",
    "        let sc_result: word = entries[sc_sender] + entries[sc_recipient] + counter;",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageLedger
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.StorageMappingExecution
/-! Execute the original checked Keccak-mapping contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Observations report
exactly the declared slots: the counter and the entry slots of every
transaction key and wrapping successor. The observer derives those slots with
the separate `Solcore.Abi.V1.Keccak256`, not with the Core builders the
contract runs, so a contract that hashed differently would write outside the
declaration. The contract's whole committed storage is reported as well. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageMappingExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)

def historySchema : String := "solcore-lean.mapping-history.v2"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  key : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256)`, followed by the flags, the
key and the input as three big-endian Words. -/
def inputData (flags key input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x24, 0xb9, 0x12, 0xe5] ++ encodeWordBytesBE flags ++ encodeWordBytesBE key ++
    encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags key input : Word) : String := encodeBytesText (inputData flags key input).bytes

/-- The pinned std's slot of `entries[key]`: `keccak256(1 ++ key)` over two
big-endian Words. The ABI digest always has 32 bytes, so the fallback is
unreachable. -/
def entrySlot (key : Word) : Word :=
  (decodeWordBytesBE? (Solcore.Abi.V1.Keccak256.hash
    (encodeWordBytesBE (Word.ofNatModulo Solcore.Synthesis.Core.StorageMapping.mappingSlot) ++
      encodeWordBytesBE key))).getD Word.zero

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The protocol's complete write set: the counter and the entry slots of each
key and each key's wrapping successor, in increasing numeric order without
duplicates. -/
def observedSlots (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => [entrySlot tx.key, entrySlot (tx.key.add (Word.ofNatModulo 1))]).foldl
    (fun slots slot => insertSlot slot slots)
    [Word.ofNatModulo Solcore.Synthesis.Core.StorageMapping.counterSlot]

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
contract or retain one invocation's local heap. A reverted invocation keeps the
prior committed world through the public runtime, not through this observer. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let slots := observedSlots transactions
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
        callValue := Word.zero, inputData := inputData transaction.flags transaction.key transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings slots),
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.StorageMappingExecution
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.StorageLedgerExecution
/-! Execute the original checked sender-keyed ledger over a persistent account
world. Unlike the other storage profiles, each transaction names its own
sender, and original Core invokes it with that caller; the world holds an empty
account for every fixed sender. Each invocation starts a fresh Core heap and
only the public terminal `finalWorld` becomes the next transaction's world.
Observations report exactly the declared slots: the counter and the entry
slots of every transaction's sender and recipient, derived with the separate
`Solcore.Abi.V1.Keccak256`, not with the Core builders the contract runs. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StorageLedgerExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan)

def historySchema : String := "solcore-lean.ledger-history.v2"

/-- The deployer and the contract address, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- Anvil's first three default accounts, in this order; the first deploys. -/
def senders : List Address := [
  ⟨1390849295786071768276380950238675083608645509734, by decide⟩,
  ⟨642829559307850963015472508762062935916233390536, by decide⟩,
  ⟨344073830386746567427978432078835137280280269756, by decide⟩]

structure Transaction where
  id : String
  sender : Address
  flags : Word
  recipient : Word
  amount : Word
  input : Word
  deriving BEq

/-- The selector of `run(uint256,uint256,uint256,uint256)`, followed by the
flags, the recipient, the amount and the input as four big-endian Words. -/
def inputData (flags recipient amount input : Word) : HostStorageDriver.InputData := {
  bytes := ByteArray.mk #[0x15, 0x50, 0x9d, 0x2b] ++ encodeWordBytesBE flags ++ encodeWordBytesBE recipient ++
    encodeWordBytesBE amount ++ encodeWordBytesBE input
  size_lt_wordModulus := by
    simp only [ByteArray.size_append, encodeWordBytesBE_size]
    decide
}

def calldata (flags recipient amount input : Word) : String :=
  encodeBytesText (inputData flags recipient amount input).bytes

/-- The entry slot of a sender: its address as a zero-extended Word, hashed
after the base slot, as the contract's `caller()` key. -/
def senderSlot (sender : Address) : Word :=
  StorageMappingExecution.entrySlot (addressToWord sender)

private def insertSlot (slot : Word) : List Word → List Word
  | [] => [slot]
  | head :: tail =>
      if slot.val < head.val then slot :: head :: tail
      else if slot.val = head.val then head :: tail
      else head :: insertSlot slot tail

/-- The protocol's complete write set: the counter and the entry slots of each
transaction's sender and recipient, in increasing numeric order without
duplicates. -/
def observedSlots (transactions : List Transaction) : List Word :=
  (transactions.flatMap fun tx => [senderSlot tx.sender, StorageMappingExecution.entrySlot tx.recipient]).foldl
    (fun slots slot => insertSlot slot slots)
    [Word.ofNatModulo Solcore.Synthesis.Core.StorageLedger.counterSlot]

/-- The deployer, the contract and an empty account for every fixed sender. -/
def initialWorld (contract : CheckedCoreContract) (bindings : Bindings) : WorldState :=
  senders.foldl (fun world sender =>
      if (world.account? sender).isSome then world else world.putAccount sender Account.empty)
    (StorageExecution.initialWorldForContract contract bindings)

private def worldStorage (world : WorldState) (bindings : Bindings) (slots : List Word) : Json :=
  match world.account? bindings.address with
  | some account => KeyedStorageExecution.storageJson account slots
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation with each transaction's own caller.
The code registry is resolved again against each current committed world, so
persistence cannot install a different contract or retain one invocation's
local heap. A reverted invocation keeps the prior committed world through the
public runtime, not through this observer. -/
def observeContract (contract : CheckedCoreContract) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json := Id.run do
  let slots := observedSlots transactions
  let registry : CheckedContractRegistry := {
    lookup := fun target => if target = bindings.address then some contract else none }
  let mut world := initialWorld contract bindings
  let initial := worldStorage world bindings slots
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let invocation : TopLevelInvocation := {
        target := bindings.address, caller := transaction.sender, callValue := Word.zero,
        inputData := inputData transaction.flags transaction.recipient transaction.amount transaction.input }
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match registry.resolve? prior bindings.address with
      | none =>
          rows := rows.push (Json.mkObj (common ++ [
            ("status", toJson "resolution-failure"),
            ("committedStorage", worldStorage prior bindings slots),
            ("accountStorage", AccountStorage.contractJson prior bindings.address)]))
          stopped := some transaction.id
      | some ⟨resolved, installed⟩ =>
          match TopLevelExecution.run resolved invocation installed fuel with
          | .completed terminal =>
              world := terminal.finalWorld
              rows := rows.push (Json.mkObj (common ++ outcomeFields terminal.outcome ++ [
                ("committedStorage", worldStorage world bindings slots),
                ("accountStorage", AccountStorage.contractJson world bindings.address)]))
          | .outOfFuel _ _ _ _ _ _ =>
              rows := rows.push (Json.mkObj (common ++ [
                ("status", toJson "out-of-fuel"),
                ("committedStorage", worldStorage prior bindings slots),
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.StorageLedgerExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageLedgerCases
/-! Sender-keyed ledger cases retain one original host-aware Core contract and
an ordered history of `(sender, flags, recipient, amount, input)` transactions
from three fixed senders. Their declared slots are derived from the senders and
recipients: the counter and the entry slot of each. Reductions remove
transactions, move one transaction to an earlier sender, replace recipients,
amounts or inputs by bank values, or simplify flags; a candidate rederives its
declared slots. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageLedger
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (Address addressToWord)
open Solcore.Synthesis.Core.StorageLedger (CheckedPlan hashNodes)
open Solcore.Synthesis.Stateful.StorageLedgerExecution (Transaction Bindings senders senderSlot)
open Solcore.Synthesis.Stateful.StorageMappingExecution (entrySlot)

def caseSchema : String := "solcore-lean.semantic-ledger-case.v1"
def planSchema : String := "solcore-lean.ledger-plan.v1"
def profileVersion : String := "stateful-ledger-v1/ledger-sequence-seed-v2"
def templateVersion : String := "sender-credit-bounded-transfer-revert-odd-flags-v1"
def ledgerCorpusSchema : String := "solcore-lean.semantic-ledger-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Recipients: the three senders, so value flows between them, the zero key,
the largest address and the largest Word. -/
def recipientBank : List Word :=
  senders.map addressToWord ++ [Word.zero, Word.ofNatModulo (2 ^ 160 - 1), Word.maximum]

/-- Bounded transfer amounts. -/
def amountBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 64 - 1), Word.ofNatModulo (2 ^ 64),
    Word.ofNatModulo (2 ^ 70)]

/-- A sender's position in the fixed order; reductions only move towards zero. -/
def senderPosition (sender : Address) : Nat := senders.idxOf sender

/-- Complete contracts may exceed the step budget by the fixed Keccak closure. -/
def maxProgramNodes : Nat := 512 + hashNodes

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => senders.contains tx.sender) = true

instance (transactions : List Transaction) : Decidable (validTransactions transactions) := by
  unfold validTransactions
  infer_instance

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ maxProgramNodes

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.StorageLedgerExecution.observedSlots scenario.transactions

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical ledger contract exceeds its case limit"
  else throw s!"ledger scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs from the fixed senders"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("sender", toJson (toString tx.sender.val)), ("flags", toJson (toString tx.flags.val)),
  ("recipient", toJson (toString tx.recipient.val)), ("amount", toJson (toString tx.amount.val)),
  ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageLedgerExecution.calldata tx.flags tx.recipient tx.amount
    tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

private def senderField (row : Json) : Except String Address := do
  let value ← wordField row "sender"
  let some sender := senders.find? (fun sender => addressToWord sender == value) |
    throw "transaction sender is not one of the fixed senders"
  return sender

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← senderField row, ← wordField row "flags",
      ← wordField row "recipient", ← wordField row "amount", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, sender, flags, recipient, amount, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "ledger scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported ledger plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "ledger contract failed full host-Core admission"
  unless json == planJson plan do throw "ledger plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "ledger contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson (scenario : CheckedScenario) : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("ledgerPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson scenario),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageLedger.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic ledger case schema"
  let plan ← checkedPlan (← json.getObjVal? "ledgerPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical ledger plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson scenario do
    throw "observed slots must be the counter and every sender's and recipient's entry slot"
  return scenario

def aliasCatalog : List String := ["self-transfer", "received-then-sent", "repeated-sender"]

/-- Static aliasing among the transactions' keys, in catalog order. This is
syntax of the sequence; it does not claim that an aliasing transfer committed. -/
def aliases (transactions : List Transaction) : List String :=
  aliasCatalog.filter fun kind =>
    if kind = "self-transfer" then transactions.any fun tx => tx.recipient == addressToWord tx.sender
    else if kind = "received-then-sent" then
      transactions.zipIdx.any fun (earlier, i) => transactions.zipIdx.any fun (later, j) =>
        i < j && earlier.recipient == addressToWord later.sender
    else (transactions.map (·.sender)).eraseDups.length < transactions.length

def distinctSenders (transactions : List Transaction) : Nat := (transactions.map (·.sender)).eraseDups.length

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageLedgerExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Odd-flags positions of the four generated patterns. Even flags may still
revert for an insufficient balance. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three senders, recipients, amounts and inputs, then the flags pattern. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. The stream starts at SplitMix64's finalizer
of the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6c65646765722d76))
  let mut values : Array Nat := #[]
  for bound in [3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 12 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), senders.getD (choices.getD index 0) ⟨0, by decide⟩, parityFlags odd,
      recipientBank.getD (choices.getD (3 + index) 0) Word.zero, amountBank.getD (choices.getD (6 + index) 0) Word.zero,
      boundaryInputs.getD (choices.getD (9 + index) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def flagsName (odd : Bool) : String := if odd then "odd" else "even"

/-- Reserve the measured protocol wrapper before generating its independent
step; the fixed Keccak closure lies outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.StorageLedger.programOverhead < nodes do
    throw "node budget is too small for the ledger wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.StorageLedger.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated ledger plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + hashNodes do
    throw "ledger contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "ledger-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceFlags", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map flagsName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

/-- The committed value of one declared slot in a storage list. -/
private def storageValue (storage : Json) (slot : Word) : Except String Nat := do
  let rows ← storage.getArr?
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some (toString slot.val)) |
    throw "committed slot missing"
  decimal entry "value"

private def wordOutput (value : Nat) : String :=
  Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE (Word.ofNatModulo value))

/-- The ledger protocol, checked from each transaction and the prior committed
slots without evaluating the step. Odd flags revert; an even-flag revert is an
insufficient balance whose payload, the credited balance, is below the amount;
a revert keeps every declared slot. A returned transaction increments the
counter, changes no declared slot but the counter and the two entries, and
returns their sum. A transfer to another key credits the recipient with
exactly the amount and leaves a sender entry the amount does not wrap; a
self-transfer leaves an entry of at least the amount. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "ledger history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "ledger history length changed"
  let counter := Word.ofNatModulo Solcore.Synthesis.Core.StorageLedger.counterSlot
  let mut prior ← history.getObjVal? "initialStorage"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    let committed ← row.getObjVal? "committedStorage"
    let output ← row.getObjValAs? String "output"
    if status == "reverted" then
      unless committed == prior do throw "a reverted ledger transaction changed the committed slots"
      unless reverts tx do
        let some payload := (Solcore.ContractRuntime.decodeBytesText? output).bind
            Solcore.ContractRuntime.decodeWordBytesBE? | throw "a ledger revert payload is not one Word"
        unless payload.val < tx.amount.val do
          throw "an even-flags ledger revert did not report an insufficient balance"
    else if status == "returned" then
      if reverts tx then throw "an odd-flags ledger transaction returned"
      let source := senderSlot tx.sender
      let target := entrySlot tx.recipient
      let count ← storageValue committed counter
      unless count == ((← storageValue prior counter) + 1) % 2 ^ 256 do
        throw "a returned ledger transaction did not increment the counter"
      let sent ← storageValue committed source
      let received ← storageValue committed target
      if source == target then
        unless tx.amount.val ≤ sent do throw "a self-transfer left an entry below the amount"
      else
        unless received == ((← storageValue prior target) + tx.amount.val) % 2 ^ 256 do
          throw "a returned ledger transfer did not credit the recipient with the amount"
        unless sent + tx.amount.val < 2 ^ 256 do throw "a returned ledger transfer wrapped the sender's entry"
      for slot in scenario.observedSlots do
        unless slot == counter || slot == source || slot == target do
          unless (← storageValue committed slot) == (← storageValue prior slot) do
            throw "a returned ledger transaction changed another declared slot"
      unless output == wordOutput ((sent + received + count) % 2 ^ 256) do
        throw "a returned ledger transaction did not return its entries and counter"
    else throw "ledger history contains an incomplete transaction"
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let _ ← checkProtocol scenario observed

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
            error == "ledger history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "ledger-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson ledgerCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Sender positions, flags, recipients, amounts and inputs all contribute; a
recipient reduction can remove aliasing. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + senderPosition transaction.sender + transaction.flags.val + transaction.recipient.val +
      transaction.amount.val + transaction.input.val) 0

/-- Transaction count, distinct senders, complete program size/literals, then
runtime sender positions, flags, recipients, amounts and inputs. Every axis is
a natural number and the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    (distinctSenders candidate.transactions < distinctSenders source.transactions ∨
    (distinctSenders candidate.transactions = distinctSenders source.transactions ∧
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

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions, then per transaction: removal, an earlier sender, bank
replacements of the recipient, the amount and the input, and flags reduced to
their parity or with the revert bit cleared. Candidates still need execution to
preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for sender in senders.take (senderPosition transaction.sender) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with sender := sender})]
    for recipient in recipientBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with recipient := recipient})]
    for amount in amountBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with amount := amount})]
    for input in boundaryInputs do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with input := input})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.StorageLedger.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from ledger plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from ledger wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "ledger-generated" then
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
      throw "saved origin differs from generated ledger provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported ledger case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson ledgerCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageLedger
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageMappingEmitter
/-! Emit the fixed Keccak-mapping protocol. The contract declares a `counter`
field at slot zero and an `entries: mapping(word => word)` field at base slot
one; the source never computes a slot itself. Indexing `entries[k]` goes
through the pinned std, which hashes the base slot followed by the key. The
entry reads and writes, the counter update, the rereads and the odd-flags
revert follow the original Core contract in order. Memory at zero is touched
only before the terminal revert, after the std's own hashing scratch use. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageMapping

open Solcore.Synthesis.Core.StorageMapping (CheckedPlan)

def emitterVersion : String := "solcore-source-keccak-mapping-v2"
def wrapperVersion : String := "solcore-word-keccak-mapping-contract-v1"
def contractName : String := "SynthesizedMapping"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256,uint256)"
def selector : String := "0x24b912e5"
def deployPath : List String := ["SynthesizedMappingDeploy"]
def runtimePath : List String := ["SynthesizedMappingDeploy", "SynthesizedMapping"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["mstore", "revert_"] (plan.step.helpers ++ [plan.step.entry]), ""]
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
    "    counter: word;",
    "    entries: mapping(word => word);",
    "",
    "    function " ++ methodName ++ "(flags: uint256, key: uint256, input: uint256) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_key: word = Typedef.rep(key);",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old: word = entries[sc_key];",
    "        entries[sc_key] = sc_step(sc_input + sc_old);",
    "        entries[sc_key + 1] = sc_old + 1;",
    "        counter = counter + 1;",
    "        let sc_result: word = entries[sc_key] + entries[sc_key + 1] + counter;",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageMapping
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageMappingCases
/-! Keccak-mapping cases retain one original host-aware Core contract and an
ordered history of `(flags, key, input)` transactions. Their declared slots
are derived from the keys: the counter and the entry slots of each key and its
wrapping successor. Reductions remove transactions, replace keys or inputs by
bank values, or simplify flags; a candidate rederives its declared slots.
Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageMapping
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageMapping (CheckedPlan hashNodes)
open Solcore.Synthesis.Stateful.StorageMappingExecution (Transaction Bindings entrySlot)

def caseSchema : String := "solcore-lean.semantic-mapping-case.v1"
def planSchema : String := "solcore-lean.mapping-plan.v1"
def profileVersion : String := "stateful-mapping-v1/mapping-sequence-seed-v2"
def templateVersion : String := "keccak-entry-successor-counter-revert-odd-flags-v1"
def mappingCorpusSchema : String := "solcore-lean.semantic-mapping-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs

/-- Mapping keys: two successor pairs, the high bit and the maximum, whose
successor wraps to zero, so generated sequences alias entries naturally. -/
def keyBank : List Word :=
  [Word.zero, Word.ofNatModulo 1, Word.ofNatModulo 6, Word.ofNatModulo 7, Word.ofNatModulo (2 ^ 255), Word.maximum]

/-- Complete contracts may exceed the step budget by the fixed Keccak closure. -/
def maxProgramNodes : Nat := 512 + hashNodes

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

def CheckedScenario.observedSlots (scenario : CheckedScenario) : List Word :=
  Solcore.Synthesis.Stateful.StorageMappingExecution.observedSlots scenario.transactions

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ maxProgramNodes then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical mapping contract exceeds its case limit"
  else throw s!"mapping scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)), ("key", toJson (toString tx.key.val)),
  ("input", toJson (toString tx.input.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.StorageMappingExecution.calldata tx.flags tx.key tx.input)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def wordField (row : Json) (key : String) : Except String Word := do
  let text ← row.getObjValAs? String key
  unless text.length ≤ 78 do throw ("transaction " ++ key ++ " exceeds a Word")
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let transaction : Transaction := ⟨← row.getObjValAs? String "id", ← wordField row "flags",
      ← wordField row "key", ← wordField row "input"⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, key, input, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "mapping scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported mapping plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "mapping contract failed full host-Core admission"
  unless json == planJson plan do throw "mapping plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "mapping contract exceeds its case limit"
  return plan

def contractJson (emitted : EmittedProgram) : Json := Json.mkObj [
  ("name", toJson emitted.contractName), ("method", toJson emitted.methodName),
  ("signature", toJson emitted.methodSignature), ("selector", toJson selector),
  ("deployPath", toJson emitted.deployPath), ("runtimePath", toJson emitted.runtimePath),
  ("constructorCalldata", toJson "0x")]

def initialStateJson : Json := Json.mkObj [("storage", toJson ([] : List Json))]

def observedSlotsJson (scenario : CheckedScenario) : Json :=
  Solcore.Synthesis.Stateful.KeyedStorageExecution.slotsJson scenario.observedSlots

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("mappingPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson scenario),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.StorageMapping.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic mapping case schema"
  let plan ← checkedPlan (← json.getObjVal? "mappingPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical mapping plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  let scenario ← checkedScenario plan transactions
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson scenario do
    throw "observed slots must be the counter and every key's and successor's entry slot"
  return scenario

def aliasCatalog : List String := ["repeated-key", "successor-key", "wrapped-successor"]

/-- Static entry aliasing among the transaction keys, in catalog order. This is
syntax of the sequence; it does not claim that an aliasing write committed. -/
def aliases (transactions : List Transaction) : List String :=
  let keys := transactions.map (·.key)
  let successor := fun (key : Word) => key.add (Word.ofNatModulo 1)
  aliasCatalog.filter fun kind =>
    if kind = "repeated-key" then keys.eraseDups.length < keys.length
    else if kind = "successor-key" then
      keys.zipIdx.any fun (left, i) => keys.zipIdx.any fun (right, j) => i != j && successor left == right
    else keys.contains Word.maximum

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageMappingExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three keys, three inputs, then the completion pattern. Each choice uses the
high half of one draw from a separate stream: the low bits of a power-of-two
LCG have short periods. The stream starts at SplitMix64's finalizer of the seed
xor its domain, so that consecutive seeds' choices do not step by a fixed
residue. -/
def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d617070696e672d))
  let mut values : Array Nat := #[]
  for bound in [6, 6, 6, 6, 6, 6, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityFlags odd, keyBank.getD (choices.getD index 0) Word.zero,
      boundaryInputs.getD (choices.getD (3 + index) 0) Word.zero⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured protocol wrapper before generating its independent
step; the fixed Keccak closure lies outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.StorageMapping.programOverhead < nodes do
    throw "node budget is too small for the mapping wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.StorageMapping.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated mapping plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + hashNodes do
    throw "mapping contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "mapping-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : Word) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some (toString slot.val)) |
    throw "committed slot missing"
  decimal entry "value"

/-- Original Core must complete every transaction with the prescribed
completion. A returned transaction increments the counter and returns the
committed entries of its key and successor plus the counter; a revert keeps
the prior slots. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "mapping history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "mapping history length changed"
  let counter := Word.ofNatModulo Solcore.Synthesis.Core.StorageMapping.counterSlot
  let mut prior ← history.getObjVal? "initialStorage"
  let mut count ← slotValue history counter "initialStorage"
  let mut statuses : List String := []
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "mapping history did not follow its flags parities"
    let committed ← row.getObjVal? "committedStorage"
    if status == "reverted" then
      unless committed == prior do throw "a reverted mapping transaction changed the committed slots"
    else
      let next ← slotValue row counter
      unless next == (count + 1) % 2 ^ 256 do throw "a returned mapping transaction did not increment the counter"
      let sum := ((← slotValue row (entrySlot tx.key)) + (← slotValue row (entrySlot (tx.key.add (Word.ofNatModulo 1)))) +
        next) % 2 ^ 256
      unless (← row.getObjValAs? String "output") ==
          Solcore.ContractRuntime.encodeBytesText (Solcore.ContractRuntime.encodeWordBytesBE (Word.ofNatModulo sum)) do
        throw "a returned mapping transaction did not return its committed entries and counter"
      count := next
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "mapping history did not follow its prescribed flags parities"

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
            error == "mapping history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "mapping-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson mappingCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Flags, keys and inputs all contribute; a key reduction can remove aliasing. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    total + transaction.flags.val + transaction.key.val + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime flags, keys
and inputs. Every axis is a natural number and the comparison is
lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      valueWeight candidate < valueWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) :
    List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions, then per transaction: removal, bank replacements of the
key and the input, and flags reduced to their parity or with the revert bit
cleared. Candidates still need execution to preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    for key in keyBank do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with key := key})]
    for input in boundaryInputs do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with input := input})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let identity := (Json.mkObj [("plan", planJson reduced.candidate.plan),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains identity then
        seen := identity :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", Solcore.Synthesis.Core.StorageMapping.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from mapping plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from mapping wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "mapping-generated" then
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
      throw "saved origin differs from generated mapping provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported mapping case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson mappingCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageMapping
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageRollbackEmitter
/-! Emit the fixed two-slot rollback protocol. Odd original inputs revert after
both writes, returning the tentative reread sum as exactly 32 bytes. Even inputs
return that same Word through the ABI. Memory at zero is touched only immediately
before the terminal revert. The arbitrary checked aggregate entry is preserved.
`ScalarMeaning.StorageRollback.emit_source_meaning` relates the emitted text to
the original Core contract's top-level transaction, returned or reverted, under
an independent rollback source semantics; see
`docs/design/scalar-emitter-meaning.md`. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageRollback

open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)

def emitterVersion : String := "solcore-source-storage-rollback-v3"
def wrapperVersion : String := "solcore-word-storage-rollback-contract-v1"
def contractName : String := "SynthesizedRollback"
def methodName : String := "run"
def methodSignature : String := "run(uint256)"
def selector : String := "0xa444f5e9"
def deployPath : List String := ["SynthesizedRollbackDeploy"]
def runtimePath : List String := ["SynthesizedRollbackDeploy", "SynthesizedRollback"]

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
    "    function " ++ methodName ++ "(input: uint256) public returns (uint256) {",
    "        let sc_input: word = Typedef.rep(input);",
    "        let sc_old0: word = sload(0);",
    "        let sc_old1: word = sload(1);",
    "        let sc_computed: word = sc_step(sc_input + sc_old0);",
    "        sstore(0, sc_computed);",
    "        sstore(1, sc_old1 + 1);",
    "        let sc_final0: word = sload(0);",
    "        let sc_final1: word = sload(1);",
    "        let sc_result: word = sc_final0 + sc_final1;",
    "        if ((sc_input & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.StorageRollback
end

section
-- leanmerge: from Solcore.Synthesis.Source.StorageRollbackCases
/-! Separate rollback cases retain the exact outcomeV1 Core contract. The odd
original ABI input reverts after both writes; the public runtime selects the
committed world. Transaction decoding and ABI metadata reuse the storage profile.
Saved outputs are never an execution oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.StorageRollback
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.StorageRollback (CheckedPlan)
open Solcore.Synthesis.Stateful.StorageExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-storage-rollback-case.v1"
def planSchema : String := "solcore-lean.storage-rollback-plan.v1"
def profileVersion : String := "stateful-storage-rollback-v2/parity-sequence-v2"
def templateVersion : String := "two-slot-feedback-revert-odd-v1"
def storageCorpusSchema : String := "solcore-lean.semantic-storage-rollback-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs
abbrev validId := Storage.validId
abbrev validTransactions := Storage.validTransactions

structure CheckedScenario where private mk ::
  plan : CheckedPlan
  transactions : List Transaction
  valid : validTransactions transactions
  bounded : Wire.programNodes plan.program ≤ 512

def CheckedScenario.program (scenario : CheckedScenario) : Wire.Program := scenario.plan.program

def checkedScenario (plan : CheckedPlan) (transactions : List Transaction) : Except String CheckedScenario := do
  if valid : validTransactions transactions then
    if bounded : Wire.programNodes plan.program ≤ 512 then
      return ⟨plan, transactions, valid, bounded⟩
    else throw "canonical storage contract exceeds the 512-node case limit"
  else throw s!"storage scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs"

abbrev transactionJson := Storage.transactionJson
abbrev transactionsJson := Storage.transactionsJson
abbrev decodeTransactions := Storage.decodeTransactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported storage plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "storage contract failed full host-Core admission"
  unless json == planJson plan do throw "storage plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "storage contract exceeds the 512-node case limit"
  return plan

abbrev contractJson := Storage.contractJson
abbrev initialStateJson := Storage.initialStateJson
abbrev observedSlotsJson := Storage.observedSlotsJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("storagePlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson), ("observedSlots", observedSlotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson StorageRollback.version), ("templateVersion", toJson templateVersion),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic storage case schema"
  let plan ← checkedPlan (← json.getObjVal? "storagePlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical storage plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == observedSlotsJson do throw "observed storage slots must be 0 and 1"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.StorageExecution.observeContract scenario.plan.contract scenario.transactions bindings fuel

abbrev sequenceIndices := Storage.sequenceIndices

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  (sequenceIndices seed).zipIdx.map fun (inputIndex, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput (index == 1) (boundaryInputs[inputIndex]?.getD Word.zero)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && StorageRollback.programOverhead < nodes do
    throw "node budget is too small for the storage wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed (nodes - StorageRollback.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated storage plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "storage contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "storage-rollback-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceIndices", toJson (Stateful.Sequence.blocks (fun blockSeed _ => sequenceIndices blockSeed) seed
      transactions)),
    ("sequenceParities", toJson (Stateful.Sequence.blocks (fun _ _ => ["even", "odd", "even"]) seed
      transactions))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "storage history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      (List.range scenario.transactions.length).map (fun index =>
        some (if index % 3 == 1 then "reverted" else "returned")) do
    throw "rollback history did not produce the prescribed return/revert/return blocks"

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
            error == "storage history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "storage-rollback-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson storageCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def inputWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.input.val) 0

/-- Transaction count, complete program size/literals, then runtime inputs.
Every axis is a natural number and the comparison is strictly lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      inputWeight candidate < inputWeight source)))

instance (candidate source : CheckedScenario) : Decidable (StrictlySmaller candidate source) := by
  unfold StrictlySmaller
  infer_instance

structure Reduction (source : CheckedScenario) where private mk ::
  candidate : CheckedScenario
  sameHelperCount : candidate.plan.step.helpers.length = source.plan.step.helpers.length
  sameBindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step
  stableIds : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id))
  strict : StrictlySmaller candidate source

private def sealReduction (source : CheckedScenario) (step : Aggregates.CheckedDAG)
    (transactions : List Transaction) : Option (Reduction source) := do
  let plan ← CheckedPlan.ofStep? step
  let candidate ← (checkedScenario plan transactions).toOption
  if count : candidate.plan.step.helpers.length = source.plan.step.helpers.length then
    if bindings : Aggregate.bindingInventory candidate.plan.step = Aggregate.bindingInventory source.plan.step then
      if ids : (candidate.transactions.map (·.id)).Sublist (source.transactions.map (·.id)) then
        if strict : StrictlySmaller candidate source then some ⟨candidate, count, bindings, ids, strict⟩
        else none
      else none
    else none
  else none

def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for index in List.range source.transactions.length do
    for input in boundaryInputs do
      let transactions := source.transactions.zipIdx.map fun (transaction, current) =>
        if current == index then {transaction with input := input} else transaction
      raw := raw ++ [(source.plan.step, transactions)]
  let mut seen : List String := []
  let mut result := []
  for (step, transactions) in raw do
    if let some reduced := sealReduction source step transactions then
      let key := (Json.mkObj [("program", Wire.encodeProgram reduced.candidate.program),
        ("transactions", transactionsJson reduced.candidate.transactions)]).compress
      if !seen.contains key then
        seen := key :: seen
        result := result ++ [reduced]
  return result

def replayCase (json : Json) (fuel : Nat) : Except String Json := do
  unless fuel ≤ 10000000 do throw "execution fuel exceeds limit"
  let admitted ← caseProgram json
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  for (name, expected) in [
      ("generatorVersion", revision.version), ("profileVersion", profileVersion),
      ("functionVersion", StorageRollback.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from storage plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from storage wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "storage-rollback-generated" then
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
      throw "saved origin differs from generated storage provenance"
    unless planJson expected.plan == planJson admitted.plan &&
        transactionsJson expected.transactions == transactionsJson admitted.transactions do
      throw "saved plan or transaction sequence differs from its generation seed"
    validateGenerated expected validationFuel
  else if kind = "imported" then
    unless origin == Json.mkObj [("kind", toJson "imported")] do throw "noncanonical imported origin"
  else if kind = "reduced" then
    let parentPlan ← checkedPlan (← origin.getObjVal? "parentPlan")
    let parentTransactions ← decodeTransactions (← origin.getObjVal? "parentTransactions")
    let parent ← checkedScenario parentPlan parentTransactions
    unless (← origin.getObjVal? "parentProgram") == Wire.encodeProgram parent.program do throw "reduction parent program differs from its plan"
    unless (sealReduction parent admitted.plan.step admitted.transactions).isSome do
      throw "reduction does not preserve bindings/IDs or decrease the complete scenario"
    unless origin == Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson parent.plan),
        ("parentProgram", Wire.encodeProgram parent.program), ("parentTransactions", transactionsJson parent.transactions)] do
      throw "noncanonical reduced origin"
  else throw "unsupported storage case origin"
  return makeCase admitted emitted origin fuel revision mask

def shrinkCases (json : Json) (limit fuel : Nat) : Except String Json := do
  let _ ← replayCase json fuel
  let source ← caseProgram json
  let origin := Json.mkObj [("kind", toJson "reduced"), ("parentPlan", planJson source.plan),
    ("parentProgram", Wire.encodeProgram source.program), ("parentTransactions", transactionsJson source.transactions)]
  -- Reductions inherit the parent case's recorded G0 revision and swarm mask.
  let provenance ← json.getObjVal? "provenance"
  let revision := savedRevision provenance
  let mask ← savedMask provenance revision
  let cases ← ((reductions source).take limit).mapM fun reduced => emitCase reduced.candidate origin fuel revision mask
  return Json.mkObj [("schema", toJson storageCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.StorageRollback
end
