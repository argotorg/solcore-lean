import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.LongBytes
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.CheckedCoreContract

/-! The long-bytes protocol behind the pinned std's dispatcher and `bytes`
decoder for `run(uint256 flags, bytes payload)`. The payload is decoded into
memory by `decodeBytesLike`: after the dispatch and head checks, the call
reverts with `ABIInputTruncated` when the payload length exceeds the bytes
after its length Word, and std's later bound `length <= ~0 - 63` can then no
longer fail. The padding after the payload is neither required nor read, so a
cut inside it is accepted and nonzero padding is ignored. The protocol then
runs on the decoded payload: chunk `k` is the aligned calldata Word masked to
the payload, or, when the cut padding leaves that Word incomplete, the Word
that ends at the last payload byte, shifted to the chunk's start. A rejection
reverts with the error selector as its Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MalformedBytes

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch

def version : String := "core-malformed-bytes-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The selector of `run(uint256,bytes)`. -/
def selector : Nat := 0x220eb9b6

/-- The std rejections this contract produces. The non-payable check cannot
fail, since no transaction carries value, and the payload is never indexed. -/
def stdErrors : List Nat := [noSelectorError, truncatedError]

/-- std's bound on a decoded `bytes` length, `~0 - 63`. -/
def maxPayloadLength : Nat := 2 ^ 256 - 64

abbrev chunkCount : Nat := LongBytes.chunkCount
abbrev countSlot : Nat := LongBytes.countSlot
abbrev tailSlot : Nat := LongBytes.tailSlot

/-- Keeps the first `remaining` bytes of a big-endian chunk Word: all of them
from 32 on, where the shift reaches 256, and none for zero. -/
private def mask (remaining : Expr) : Expr :=
  .unary .wordNot (.binary .wordShr (word (2 ^ 256 - 1)) (mul (word 8) remaining))

/-- Chunk `index` in a frame of `index + 6` binders: the newest accumulator is
local zero, the length local `index + 1`, the head offset local `index + 2`,
the flags local `index + 3`, the size local `index + 4` and the step local
`index + 5`. Either case branch binds one payload. -/
private def chunkWord (index : Nat) : Expr :=
  .caseE (host 8 (index + 6) (add (.var (index + 2)) (word (36 + 32 * index))))
    (.binary .wordShl
      (readAt (index + 7) (add (.var (index + 3)) (add (.var (index + 2)) (word 4))))
      (mul (word 8) (sub (word (32 * (index + 1))) (.var (index + 2)))))
    (.binary .wordAnd (.var 0) (mask (sub (.var (index + 2)) (word (32 * index)))))

private def chunk (index : Nat) : Expr :=
  .ifE (gt (.var (index + 1)) (word (32 * index)))
    (.letE (chunkWord index)
      (.letE (.apply (.var (index + 6)) (add (.var 1) (.var 0)))
        (.letE (host 1 (index + 8) (.pair (word (index + 1)) (.var 0)))
          (.var 1))))
    (.var 0)

/-- After `chunks` chunks the length is local `chunks + 1` and the offset local
`chunks + 2`; the last payload byte sits at `4 + offset + 32 + length - 1`. -/
private def tail (chunks : Nat) : Expr :=
  .ifE (gt (.var (chunks + 1)) (word 0))
    (.caseE (host 6 (chunks + 6) (add (.var (chunks + 2)) (add (.var (chunks + 1)) (word 35)))) (word 0) (.var 0))
    (word 0)

/-- After the result binding, the flags are local `chunks + 9`. -/
private def completion (chunks : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var (chunks + 9)) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- The tail, the writes of slot zero, the count slot and the tail slot, the
rereads with the calldata size and the completion, after all chunk binders. -/
private def finish (chunks : Nat) : Expr :=
  .letE (tail chunks)
    (.letE (host 1 (chunks + 7) (.pair (word 0) (.var 1)))
      (.letE (add (host 0 (chunks + 8) (word countSlot)) (.var (chunks + 3)))
        (.letE (host 1 (chunks + 9) (.pair (word countSlot) (.var 0)))
          (.letE (host 1 (chunks + 10) (.pair (word tailSlot) (.var 3)))
            (.letE (add (add (add (host 0 (chunks + 11) (word 0)) (host 0 (chunks + 11) (word countSlot)))
                  (host 0 (chunks + 11) (word tailSlot)))
                (host 7 (chunks + 11) .unit))
              (completion chunks))))))

/-- Chunks `index` through `chunks - 1`, each bound in turn, then `finish`. -/
private def chunked (chunks : Nat) : Nat → Nat → Expr
  | 0, _ => finish chunks
  | remaining + 1, index => .letE (chunk index) (chunked chunks remaining (index + 1))

/-- std's dispatch, head and payload checks in its order, then the chunks. -/
private def contractExpressionWith (chunks : Nat) (stepBody : Expr) : Expr :=
  dynamicHead selector stepBody
    (.letE (readAt 4 (add (word 4) (.var 0)))
      (.ifE (gt (.var 0) (sub (.var 3) (add (word 36) (.var 1)))) (reject truncatedError)
        (.ifE (gt (.var 0) (word maxPayloadLength)) (reject truncatedError)
          (.letE (host 0 5 (word 0))
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

/-- The std checks and protocol wrapper around the step without the chunk guards. -/
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
end Solcore.Synthesis.Core.MalformedBytes
