import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked protocol over one bounded dynamic `bytes` value. The calldata of
`run(uint256 flags, bytes payload)` is decoded by following the head offset to
the payload length, as the ABI does. Each present 32-byte chunk, at most two,
is read as one Word masked to the payload length and folded through a closed
aggregate step, chunk `k` writing slot `1 + k`. The accumulator is written to
slot zero, a running byte count to slot three and the last payload byte to slot
four; the result adds those slots, read back, to the calldata size. The original
flags parity then selects return or revert. The public contract runtime commits
or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.DynamicBytes

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-dynamic-bytes-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Payload bytes beyond this bound are never read by either the Core contract
or the emitted source; the case boundary admits at most this many. -/
def maxPayloadBytes : Nat := 64

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)
/-- An absent calldata byte reads as zero, likewise. -/
private def byteAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 6 locals address) (word 0) (.var 0)

/-- Keeps the first `remaining` bytes of a big-endian chunk Word: all of them
from 32 on, where the shift reaches 256, and none for zero. -/
private def mask (remaining : Expr) : Expr :=
  .unary .wordNot (.binary .wordShr (word (2 ^ 256 - 1)) (.binary .wordMul (word 8) remaining))

/-- Chunk `index` exists in a frame of `index + 5` binders, where the newest
accumulator is local zero, the length is local `index + 1`, the head offset is
local `index + 2` and the step is local `index + 4`. The chunk starts one length
Word past the offset relative to the arguments, which start at byte 4, so bytes
at or past the length, the ABI's zero padding, never contribute. -/
private def chunk (index : Nat) : Expr :=
  .ifE (.binary .wordGt (.var (index + 1)) (word (32 * index)))
    (.letE (.binary .wordAnd
        (readAt (index + 5) (.binary .wordAdd (.var (index + 2)) (word (36 + 32 * index))))
        (mask (.binary .wordSub (.var (index + 1)) (word (32 * index)))))
      (.letE (.apply (.var (index + 5)) (.binary .wordAdd (.var 1) (.var 0)))
        (.letE (host 1 (index + 7) (.pair (word (index + 1)) (.var 0)))
          (.var 1))))
    (.var 0)

/-- After both chunks, the length is local three and the offset local four; the
last payload byte sits at `4 + offset + 32 + length - 1`. -/
private def tail : Expr :=
  .ifE (.binary .wordGt (.var 3) (word 0))
    (byteAt 7 (.binary .wordAdd (.var 4) (.binary .wordAdd (.var 3) (word 35))))
    (word 0)

/-- After the result binding, the flags are local eleven; the length, offset,
all three accumulators, the tail, the total and the three Unit write binders
remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 11) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readAt 1 (word 4))
      (.letE (readAt 2 (word 36))
        (.letE (readAt 3 (.binary .wordAdd (word 4) (.var 0)))
          (.letE (host 0 4 (word 0))
            (.letE (chunk 0)
              (.letE (chunk 1)
                (.letE tail
                  (.letE (host 1 8 (.pair (word 0) (.var 1)))
                    (.letE (.binary .wordAdd (host 0 9 (word 3)) (.var 5))
                      (.letE (host 1 10 (.pair (word 3) (.var 0)))
                        (.letE (host 1 11 (.pair (word 4) (.var 3)))
                          (.letE (.binary .wordAdd
                              (.binary .wordAdd (.binary .wordAdd (host 0 12 (word 0)) (host 0 12 (word 3)))
                                (host 0 12 (word 4)))
                              (host 7 12 .unit))
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
end Solcore.Synthesis.Core.DynamicBytes
