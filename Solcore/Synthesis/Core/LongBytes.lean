import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! The bytes protocol of `DynamicBytes` over up to eight 32-byte chunks, so a
`bytes` payload reaches 256 bytes. The calldata of `run(uint256 flags, bytes
payload)` is decoded by following the head offset to the payload length, as
the ABI does. Each present chunk is read as one Word masked to the payload
length and folded through a closed aggregate step, chunk `k` writing slot
`1 + k`. The accumulator is written to slot zero, a running byte count to slot
nine and the last payload byte to slot ten; the result adds those slots, read
back, to the calldata size. The original flags parity then selects return or
revert. The public contract runtime commits or rolls back the resulting
working world. With two chunks and slots three and four for the count and the
last byte, this is exactly the `DynamicBytes` contract. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.LongBytes

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-long-bytes-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Chunks read by the contract; payload bytes beyond them are never read by
either the Core contract or the emitted source, and the case boundary admits
at most `maxPayloadBytes`. -/
def chunkCount : Nat := 8
def maxPayloadBytes : Nat := 32 * chunkCount

/-- Slot zero holds the accumulator and slot `1 + k` chunk `k`'s result; the
running byte count and the last payload byte follow the chunk slots. -/
def countSlot : Nat := chunkCount + 1
def tailSlot : Nat := chunkCount + 2

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

/-- After `chunks` chunks the length is local `chunks + 1` and the offset local
`chunks + 2`; the last payload byte sits at `4 + offset + 32 + length - 1`. -/
private def tail (chunks : Nat) : Expr :=
  .ifE (.binary .wordGt (.var (chunks + 1)) (word 0))
    (byteAt (chunks + 5) (.binary .wordAdd (.var (chunks + 2)) (.binary .wordAdd (.var (chunks + 1)) (word 35))))
    (word 0)

/-- After the result binding, the flags are local `chunks + 9`. -/
private def completion (chunks : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var (chunks + 9)) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- The tail, the writes of slots zero, `chunks + 1` and `chunks + 2`, the
rereads and the completion, after all chunk binders. -/
private def finish (chunks : Nat) : Expr :=
  .letE (tail chunks)
    (.letE (host 1 (chunks + 6) (.pair (word 0) (.var 1)))
      (.letE (.binary .wordAdd (host 0 (chunks + 7) (word (chunks + 1))) (.var (chunks + 3)))
        (.letE (host 1 (chunks + 8) (.pair (word (chunks + 1)) (.var 0)))
          (.letE (host 1 (chunks + 9) (.pair (word (chunks + 2)) (.var 3)))
            (.letE (.binary .wordAdd
                (.binary .wordAdd (.binary .wordAdd (host 0 (chunks + 10) (word 0))
                  (host 0 (chunks + 10) (word (chunks + 1)))) (host 0 (chunks + 10) (word (chunks + 2))))
                (host 7 (chunks + 10) .unit))
              (completion chunks))))))

/-- Chunks `index` through `chunks - 1`, each bound in turn, then `finish`. -/
private def chunked (chunks : Nat) : Nat → Nat → Expr
  | 0, _ => finish chunks
  | remaining + 1, index => .letE (chunk index) (chunked chunks remaining (index + 1))

private def contractExpressionWith (chunks : Nat) (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readAt 1 (word 4))
      (.letE (readAt 2 (word 36))
        (.letE (readAt 3 (.binary .wordAdd (word 4) (.var 0)))
          (.letE (host 0 4 (word 0))
            (chunked chunks chunks 0)))))

private def contractExpression (stepBody : Expr) : Expr := contractExpressionWith chunkCount stepBody

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead with `chunks` chunk guards; the placeholder is never
admitted or run. -/
private def overheadWith (chunks : Nat) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpressionWith chunks (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The fixed chunk guards' size, which lies outside the step's node budget. -/
def guardNodes : Nat := overheadWith chunkCount - overheadWith 0

/-- The protocol wrapper around the step without the chunk guards. -/
def programOverhead : Nat := overheadWith 0

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
end Solcore.Synthesis.Core.LongBytes
