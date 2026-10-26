import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.Core.Wire.Conversions
import Solcore.ContractRuntime.CheckedCoreContract
import Solcore.Frontend.RustHull.Keccak

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
