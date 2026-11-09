import Solcore.Synthesis.Internal.Aggregates
import Solcore.Core.Wire.Codec
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Synthesis.Internal.Storage
import Solcore.Synthesis.Stateful.Sequence

/-!
# Profiles: dynamic ABI values

The profiles `stateful-dynamic-array`, `stateful-bytes`, `stateful-long-bytes` and
`stateful-nested-array`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.DynamicArray
/-! A checked protocol over one bounded dynamic ABI value. The calldata of
`run(uint256 flags, uint256[] values)` is decoded by following the head offset
to the array length, as the ABI does. At most three elements are folded through
a closed aggregate step, element `i` writing slot `1 + i`; the accumulator is
written to slot zero and a running element count to slot four. The original
flags parity then selects return or revert. The public contract runtime commits
or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.DynamicArray

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-dynamic-array-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Elements beyond this bound are never read by either the Core contract or
the emitted source; the case boundary admits at most this many. -/
def maxElements : Nat := 3

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- Element `index` exists in a frame with `locals` binders, where the newest
accumulator is local zero, the length is local `index + 1`, the head offset is
local `index + 2` and the step is local `index + 4`. The element Word lives one
length word past the offset relative to the arguments, which start at byte 4. -/
private def element (index locals : Nat) : Expr :=
  .ifE (.binary .wordGt (.var (index + 1)) (word index))
    (.letE (readAt locals (.binary .wordAdd (.binary .wordAdd (word 4) (.var (index + 2))) (word (32 * (index + 1)))))
      (.letE (.apply (.var (index + 5)) (.binary .wordAdd (.var 1) (.var 0)))
        (.letE (host 1 (locals + 2) (.pair (word (index + 1)) (.var 0)))
          (.var 1))))
    (.var 0)

/-- After the result binding, the flags are local ten; the length, offset,
all four accumulators and both Unit write binders remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readAt 1 (word 4))
      (.letE (readAt 2 (word 36))
        (.letE (readAt 3 (.binary .wordAdd (word 4) (.var 0)))
          (.letE (host 0 4 (word 0))
            (.letE (element 0 5)
              (.letE (element 1 6)
                (.letE (element 2 7)
                  (.letE (host 1 8 (.pair (word 0) (.var 0)))
                    (.letE (.binary .wordAdd (host 0 9 (word 4)) (.var 5))
                      (.letE (host 1 10 (.pair (word 4) (.var 0)))
                        (.letE (.binary .wordAdd (host 0 11 (word 0)) (host 0 11 (word 4)))
                          completion)))))))))))

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
end Solcore.Synthesis.Core.DynamicArray
end

section
-- leanmerge: from Solcore.Synthesis.Core.DynamicBytes
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.LongBytes
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.NestedArray
/-! A checked protocol over one bounded nested dynamic array. The calldata of
`run(uint256 flags, uint256[][] values)` is decoded as the ABI does: the head
offset leads to the outer length and a table of row offsets, measured from the
start of that table, and each row offset leads to the row's length and
elements. Each present element `(i, j)`, at most three rows of at most two
elements, is folded through a closed aggregate step and written to slot
`1 + 2i + j`. The accumulator is written to slot zero, a running row count to
slot seven and a running element count to slot eight; the result adds those
slots, read back. The original flags parity then selects return or revert. The
public contract runtime commits or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.NestedArray

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-nested-array-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- Rows and elements per row read by the contract; the case boundary admits no more. -/
def maxRows : Nat := 3
def maxColumns : Nat := 2

/-- Slot zero holds the accumulator and slot `1 + 2i + j` element `(i, j)`'s
result; the running row and element counts follow the element slots. -/
def rowSlot : Nat := 1 + maxColumns * maxRows
def cellSlot : Nat := 2 + maxColumns * maxRows

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)
/-- The binder at position `position`, counted from the outermost, seen from a
frame of `locals` binders. -/
private def binder (locals position : Nat) : Expr := .var (locals - 1 - position)

/- Binder positions: the step 0, the flags 1, the head offset 2, the outer
length 3 and the initial accumulator 4. Row `i` then binds its start `5 + bi`,
its length `6 + bi` and its elements' accumulators `7 + bi + j`, where `b` is
`maxColumns + 2`. -/
private def block : Nat := maxColumns + 2
private def rowStart (row : Nat) : Nat := 5 + block * row
private def rowLength (row : Nat) : Nat := 6 + block * row
private def cellAcc (row column : Nat) : Nat := 7 + block * row + column
/-- The accumulator before element `(i, j)`: the previous element's, or the
initial one before row zero. -/
private def accBefore (row column : Nat) : Nat :=
  if column = 0 then 4 + block * row else cellAcc row (column - 1)

/-- The absolute byte position of row `i`'s length Word: past the selector at
`4 + offset`, the outer length and then the row's table offset. -/
private def startOf (row : Nat) (locals : Nat) : Expr :=
  .ifE (.binary .wordGt (binder locals 3) (word row))
    (.binary .wordAdd (.binary .wordAdd (binder locals 2) (word 36))
      (readAt locals (.binary .wordAdd (.binary .wordAdd (binder locals 2) (word 36)) (word (32 * row)))))
    (word 0)

private def lengthOf (row : Nat) (locals : Nat) : Expr :=
  .ifE (.binary .wordGt (binder locals 3) (word row)) (readAt locals (binder locals (rowStart row))) (word 0)

/-- Element `(i, j)`, present when the row's length exceeds `j`: fold it through
the step and write its slot; otherwise keep the accumulator. -/
private def cell (row column : Nat) (locals : Nat) : Expr :=
  .ifE (.binary .wordGt (binder locals (rowLength row)) (word column))
    (.letE (readAt locals (.binary .wordAdd (binder locals (rowStart row)) (word (32 + 32 * column))))
      (.letE (.apply (binder (locals + 1) 0) (.binary .wordAdd (binder (locals + 1) (accBefore row column)) (.var 0)))
        (.letE (host 1 (locals + 2) (.pair (word (1 + maxColumns * row + column)) (.var 0)))
          (.var 1))))
    (binder locals (accBefore row column))

/-- Each row's start, length and elements in turn, then `finish`. -/
private def rowsFrom (rows : Nat) (finish : Nat → Expr) : Nat → Nat → Expr
  | 0, _ => finish rows
  | remaining + 1, row =>
      let locals := rowStart row
      .letE (startOf row locals)
        (.letE (lengthOf row (locals + 1))
          ((List.range maxColumns).foldr
            (fun column body => .letE (cell row column (locals + 2 + column)) body)
            (rowsFrom rows finish remaining (row + 1))))

/-- After `rows` rows: the element count, the slot writes, the rereads and the
completion. -/
private def finish (rows : Nat) : Expr :=
  let locals := 5 + block * rows
  let cells := (List.range rows).foldl (fun total row => .binary .wordAdd total (binder locals (rowLength row))) (word 0)
  .letE cells
    (.letE (host 1 (locals + 1) (.pair (word 0) (binder (locals + 1) (4 + block * rows))))
      (.letE (host 1 (locals + 2) (.pair (word (1 + maxColumns * rows))
          (.binary .wordAdd (host 0 (locals + 2) (word (1 + maxColumns * rows))) (binder (locals + 2) 3))))
        (.letE (host 1 (locals + 3) (.pair (word (2 + maxColumns * rows))
            (.binary .wordAdd (host 0 (locals + 3) (word (2 + maxColumns * rows))) (binder (locals + 3) locals))))
          (.letE (.binary .wordAdd
              (.binary .wordAdd (host 0 (locals + 4) (word 0)) (host 0 (locals + 4) (word (1 + maxColumns * rows))))
              (host 0 (locals + 4) (word (2 + maxColumns * rows))))
            (.ifE (.binary .wordEq (.binary .wordAnd (binder (locals + 5) 1) (word 1)) (word 1))
              (.inRight .word (.inLeft .word (.var 0)))
              (.inLeft (.sum .word .word) (.var 0)))))))

private def contractExpressionWith (rows : Nat) (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readAt 1 (word 4))
      (.letE (readAt 2 (word 36))
        (.letE (readAt 3 (.binary .wordAdd (word 4) (.var 0)))
          (.letE (host 0 4 (word 0))
            (rowsFrom rows finish rows 0)))))

private def contractExpression (stepBody : Expr) : Expr := contractExpressionWith maxRows stepBody

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead with `rows` row guards; the placeholder is never
admitted or run. -/
private def overheadWith (rows : Nat) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpressionWith rows (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The fixed row and element guards' size, which lies outside the step's node budget. -/
def guardNodes : Nat := overheadWith maxRows - overheadWith 0

/-- The protocol wrapper around the step without the row and element guards. -/
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
end Solcore.Synthesis.Core.NestedArray
end

section
-- leanmerge: from Solcore.Synthesis.Source.DynamicArrayEmitter
/-! Emit the fixed dynamic-array protocol. The ABI parameter is a lazily decoded
calldata array, so `values.length()` reads the same length word as the Core
contract and `values[i]` decodes element `i` only inside the branch that the
length admits. The three element branches, the slot writes, the counter update
and the odd-flags revert follow the original Core contract in order. Memory at
zero is touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicArray

open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)

def emitterVersion : String := "solcore-source-dynamic-array-v3"
def wrapperVersion : String := "solcore-word-dynamic-array-contract-v1"
def contractName : String := "SynthesizedDynamicArray"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256[])"
def selector : String := "0x9a94c44b"
def deployPath : List String := ["SynthesizedDynamicArrayDeploy"]
def runtimePath : List String := ["SynthesizedDynamicArrayDeploy", "SynthesizedDynamicArray"]

private def elementLines (index : Nat) : List String :=
  let i := toString index
  ["        if (sc_length > " ++ i ++ ") {",
    "            let sc_value" ++ i ++ ": word = Typedef.rep(values[uint256(" ++ i ++ ")]);",
    "            sc_acc = sc_step(sc_acc + sc_value" ++ i ++ ");",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);",
    "        }"]

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
    "    function " ++ methodName ++ "(flags: uint256, values: calldata<array<uint256>>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_length: word = Typedef.rep(values.length());",
    "        let sc_acc: word = sload(0);"] ++
    ((List.range Solcore.Synthesis.Core.DynamicArray.maxElements).flatMap elementLines) ++ [
    "        sstore(0, sc_acc);",
    "        let sc_total: word = sload(4) + sc_length;",
    "        sstore(4, sc_total);",
    "        let sc_result: word = sload(0) + sload(4);",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.DynamicArray
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.DynamicArrayExecution
/-! Execute the original checked dynamic-array contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Calldata is the
canonical ABI encoding of `(flags, values)`: the static head, the array offset
64, the length and the elements. Observations report the five declared slots
and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.DynamicArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)

def historySchema : String := "solcore-lean.dynamic-array-history.v2"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  values : List Word
  deriving BEq

/-- The selector of `run(uint256,uint256[])`, the flags Word, the tail offset
64 relative to the arguments, the length and the element Words. -/
def inputBytes (flags : Word) (values : List Word) : ByteArray :=
  values.foldl (fun bytes value => bytes ++ encodeWordBytesBE value)
    (ByteArray.mk #[0x9a, 0x94, 0xc4, 0x4b] ++ encodeWordBytesBE flags ++
      encodeWordBytesBE (Word.ofNatModulo 64) ++ encodeWordBytesBE (Word.ofNatModulo values.length))

/-- Bounded cases are far below the Word-sized calldata limit; the check keeps
the runtime input total without assuming the case boundary. -/
def inputData? (flags : Word) (values : List Word) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes flags values
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

def calldata (flags : Word) (values : List Word) : String := encodeBytesText (inputBytes flags values)

/-- Slot zero holds the accumulator, slots one to three the per-element
results and slot four the running element count. -/
def observedSlots : List Word := (List.range 5).map Word.ofNatModulo

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
      match inputData? transaction.flags transaction.values, registry.resolve? prior bindings.address with
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.DynamicArrayExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.DynamicArrayCases
/-! Dynamic-array cases retain one original host-aware Core contract and an
ordered history of `(flags, values)` transactions, each with zero to three
elements in its canonical ABI encoding. Reductions remove transactions or array
elements and simplify flags or elements. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicArray
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.DynamicArray (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicArrayExecution (Transaction Bindings)

def caseSchema : String := "solcore-lean.semantic-dynamic-array-case.v1"
def planSchema : String := "solcore-lean.dynamic-array-plan.v1"
def profileVersion : String := "stateful-dynamic-array-v2/array-sequence-seed-v2"
def templateVersion : String := "array-fold-slots-count-revert-odd-flags-v1"
def arrayCorpusSchema : String := "solcore-lean.semantic-dynamic-array-corpus.v1"

/-- Element and flags values; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.values.length ≤ Solcore.Synthesis.Core.DynamicArray.maxElements) = true

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
    else throw "canonical dynamic-array contract exceeds the 512-node case limit"
  else throw s!"dynamic-array scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and at most three elements each"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun value => toString value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.DynamicArrayExecution.calldata tx.flags tx.values)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List String) "values"
    unless texts.length ≤ Solcore.Synthesis.Core.DynamicArray.maxElements do throw "array exceeds three elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM word⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "dynamic-array scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported dynamic-array plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "dynamic-array contract failed full host-Core admission"
  unless json == planJson plan do throw "dynamic-array plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "dynamic-array contract exceeds the 512-node case limit"
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
    ("schema", toJson caseSchema), ("dynamicArrayPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.DynamicArrayExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.DynamicArray.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic dynamic-array case schema"
  let plan ← checkedPlan (← json.getObjVal? "dynamicArrayPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical dynamic-array plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.DynamicArrayExecution.slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.DynamicArrayExecution.observe scenario.plan scenario.transactions bindings fuel

def parityInput (odd : Bool) (input : Word) : Word :=
  if odd then input.bitOr (Word.ofNatModulo 1)
  else input.bitAnd (Word.ofNatModulo (2 ^ 256 - 2))

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three lengths, three flags, nine elements, then the completion pattern.
Each choice uses the high half of one draw from a separate stream. The stream
starts at SplitMix64's finalizer of the seed xor its domain, so that consecutive
seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := [4, 4, 4] ++ List.replicate 12 6 ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x64796e2d61727279))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 15 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityInput odd (bank (3 + index)),
      ((List.range (choices.getD index 0)).map fun position => bank (6 + 3 * index + position))⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.DynamicArray.programOverhead < nodes do
    throw "node budget is too small for the dynamic-array wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.DynamicArray.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated dynamic-array plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "dynamic-array contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "dynamic-array-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "dynamic-array history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.map (fun row => (row.getObjValAs? String "status").toOption) ==
      scenario.transactions.map (fun tx => some (statusName (tx.flags.val % 2 == 1))) do
    throw "dynamic-array history did not follow its prescribed flags parities"

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
            error == "dynamic-array history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "dynamic-array-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson arrayCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def elementCount (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.values.length) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum value => sum + value.val) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the number of array
elements, then flags and element values. Every axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (elementCount candidate < elementCount source ∨
      (elementCount candidate = elementCount source ∧ valueWeight candidate < valueWeight source)))))

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

private def replaceAt (transactions : List Transaction) (index : Nat) (change : Transaction → Transaction) : List Transaction :=
  transactions.zipIdx.map fun (transaction, current) => if current == index then change transaction else transaction

/-- Step reductions, then per transaction: removal, removal of each element,
and bank replacements of each element and of the flags. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  -- Removing one transaction comes first, from the last back: a long
  -- sequence loses the tail beyond a difference before the candidate limit.
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    for position in List.range transaction.values.length do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
        {tx with values := tx.values.eraseIdx position})]
    for position in List.range transaction.values.length do
      for value in boundaryInputs do
        raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx =>
          {tx with values := tx.values.set position value})]
    for flags in boundaryInputs do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with flags := flags})]
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
      ("functionVersion", Solcore.Synthesis.Core.DynamicArray.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from dynamic-array plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from dynamic-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "dynamic-array-generated" then
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
      throw "saved origin differs from generated dynamic-array provenance"
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
  else throw "unsupported dynamic-array case origin"
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
  return Json.mkObj [("schema", toJson arrayCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.DynamicArray
end

section
-- leanmerge: from Solcore.Synthesis.Source.DynamicBytesEmitter
/-! Emit the fixed bytes protocol. The pinned ABI decoder produces `bytes` only
in memory: it follows the head offset, copies the length Word and the payload
into fresh memory and zeroes the padding to a whole Word. The source therefore
reads chunk `k` as the zero-padded memory Word `mload(data + 32 + 32k)` and the
last payload byte through the unaligned Word that ends at it, whose low byte is
zero for an empty payload. The two chunk branches, the slot writes and the
odd-flags revert follow the original Core contract in order. Memory at zero is
touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicBytes

open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)

def emitterVersion : String := "solcore-source-dynamic-bytes-v2"
def wrapperVersion : String := "solcore-word-dynamic-bytes-contract-v1"
def contractName : String := "SynthesizedBytes"
def methodName : String := "run"
def methodSignature : String := "run(uint256,bytes)"
def selector : String := "0x220eb9b6"
def deployPath : List String := ["SynthesizedBytesDeploy"]
def runtimePath : List String := ["SynthesizedBytesDeploy", "SynthesizedBytes"]

private def chunkLines (index : Nat) : List String :=
  ["        if (sc_length > " ++ toString (32 * index) ++ ") {",
    "            sc_acc = sc_step(sc_acc + mload(sc_data + " ++ toString (32 * (index + 1)) ++ "));",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);",
    "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_", "mload", "calldatasize"]
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
    "    function " ++ methodName ++ "(flags: uint256, payload: memory<bytes>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_data: word = Typedef.rep(payload);",
    "        let sc_length: word = mload(sc_data);",
    "        let sc_acc: word = sload(0);"] ++ chunkLines 0 ++ chunkLines 1 ++ [
    "        let sc_tail: word = mload(sc_data + sc_length) & 255;",
    "        sstore(0, sc_acc);",
    "        let sc_total: word = sload(3) + sc_length;",
    "        sstore(3, sc_total);",
    "        sstore(4, sc_tail);",
    "        let sc_result: word = sload(0) + sload(3) + sload(4) + calldatasize();",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.DynamicBytes
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.DynamicBytesExecution
/-! Execute the original checked bytes contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Calldata is the canonical
ABI encoding of `(flags, payload)`: the static head, the tail offset 64, the
length, the payload bytes and zero padding to a whole Word. Observations report
the five declared slots and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.DynamicBytesExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan)

def historySchema : String := "solcore-lean.bytes-history.v2"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

structure Transaction where
  id : String
  flags : Word
  payload : List UInt8
  deriving BEq

/-- Payload bytes padded with zeros to a whole number of Words. -/
def paddedLength (length : Nat) : Nat := (length + 31) / 32 * 32

/-- The selector of `run(uint256,bytes)`, the flags Word, the tail offset 64
relative to the arguments, the length, the payload and its zero padding. -/
def inputBytes (flags : Word) (payload : List UInt8) : ByteArray :=
  ByteArray.mk #[0x22, 0x0e, 0xb9, 0xb6] ++ encodeWordBytesBE flags ++
    encodeWordBytesBE (Word.ofNatModulo 64) ++ encodeWordBytesBE (Word.ofNatModulo payload.length) ++
    ByteArray.mk (payload ++ List.replicate (paddedLength payload.length - payload.length) 0).toArray

/-- Bounded cases are far below the Word-sized calldata limit; the check keeps
the runtime input total without assuming the case boundary. -/
def inputData? (flags : Word) (payload : List UInt8) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes flags payload
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

def calldata (flags : Word) (payload : List UInt8) : String := encodeBytesText (inputBytes flags payload)

/-- Slot zero holds the accumulator, slots one and two the per-chunk results,
slot three the running byte count and slot four the last payload byte. -/
def observedSlots : List Word := (List.range 5).map Word.ofNatModulo

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
      match inputData? transaction.flags transaction.payload, registry.resolve? prior bindings.address with
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.DynamicBytesExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.DynamicBytesCases
/-! Bytes cases retain one original host-aware Core contract and an ordered
history of `(flags, payload)` transactions, each payload of zero to 64 bytes in
its canonical ABI encoding. Reductions remove transactions, truncate a payload
to a shorter bank length, zero its bytes or simplify flags. Saved outputs are
never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.DynamicBytes
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.DynamicBytes (CheckedPlan maxPayloadBytes)
open Solcore.Synthesis.Stateful.DynamicBytesExecution (Transaction Bindings paddedLength)
open Solcore.ContractRuntime (encodeBytesText decodeBytesText? encodeWordBytesBE)

def caseSchema : String := "solcore-lean.semantic-bytes-case.v1"
def planSchema : String := "solcore-lean.bytes-plan.v1"
def profileVersion : String := "stateful-bytes-v1/bytes-sequence-seed-v2"
def templateVersion : String := "bytes-chunks-tail-size-revert-odd-flags-v1"
def bytesCorpusSchema : String := "solcore-lean.semantic-bytes-corpus.v1"

/-- Payload lengths: empty, one byte, inside the first chunk, both sides of the
Word boundary, inside the second chunk, one short of the bound and the bound. -/
def lengthBank : List Nat := [0, 1, 17, 31, 32, 33, 48, 63, 64]

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.payload.length ≤ maxPayloadBytes) = true

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
    else throw "canonical bytes contract exceeds the 512-node case limit"
  else throw s!"bytes scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and payloads of at most 64 bytes"

def payloadText (payload : List UInt8) : String := encodeBytesText (ByteArray.mk payload.toArray)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("payload", toJson (payloadText tx.payload)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.DynamicBytesExecution.calldata tx.flags tx.payload)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let text ← row.getObjValAs? String "payload"
    unless text.length ≤ 2 + 2 * maxPayloadBytes do throw "payload exceeds 64 bytes"
    let some bytes := decodeBytesText? text | throw "payload is not canonical lowercase hexadecimal"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), bytes.data.toList⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, payload, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "bytes scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported bytes plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "bytes contract failed full host-Core admission"
  unless json == planJson plan do throw "bytes plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "bytes contract exceeds the 512-node case limit"
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
    ("schema", toJson caseSchema), ("bytesPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.DynamicBytesExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.DynamicBytes.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic bytes case schema"
  let plan ← checkedPlan (← json.getObjVal? "bytesPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical bytes plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.DynamicBytesExecution.slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.DynamicBytesExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three lengths, three byte patterns, then the completion pattern. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. The stream starts at SplitMix64's finalizer
of the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def sequenceBounds : List Nat := [9, 9, 9, 4, 4, 4, 4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x62797465732d7478))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Sixty-four seeded bytes for each of three transactions from a further
stream; each draw contributes the four bytes of its high half. The stream starts
at SplitMix64's finalizer of the seed xor its domain, so that consecutive seeds'
bytes are not affine in the seed. -/
def seededPayloads (seed : Seed) : List (List UInt8) := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x62797465732d6461))
  let mut payloads : Array (List UInt8) := #[]
  for _ in List.range 3 do
    let mut bytes : Array UInt8 := #[]
    for _ in List.range 16 do
      let (value, next) := state.draw
      let high := value.toNat / 2 ^ 32
      bytes := bytes ++ #[(high / 2 ^ 24 % 256).toUInt8, (high / 2 ^ 16 % 256).toUInt8,
        (high / 2 ^ 8 % 256).toUInt8, (high % 256).toUInt8]
      state := next
    payloads := payloads.push bytes.toList
  return payloads.toList

/-- Zeros, `0xff`, the ramp `1, 2, 3, ...` or the seeded bytes, cut to `length`. -/
def patternBytes (pattern length : Nat) (seeded : List UInt8) : List UInt8 :=
  match pattern with
  | 0 => List.replicate length 0
  | 1 => List.replicate length 0xff
  | 2 => (List.range length).map fun position => (position + 1).toUInt8
  | _ => seeded.take length

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let seeded := seededPayloads seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityFlags odd,
      patternBytes (choices.getD (3 + index) 0) (lengthBank.getD (choices.getD index 0) 0) (seeded.getD index [])⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.DynamicBytes.programOverhead < nodes do
    throw "node budget is too small for the bytes wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.DynamicBytes.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated bytes plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "bytes contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "bytes-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : String) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some slot) |
    throw "committed slot missing"
  decimal entry "value"

/-- The last payload byte, or zero for an empty payload. -/
def tailByte (payload : List UInt8) : Nat := (payload.getLast?.map UInt8.toNat).getD 0

/-- Selector, flags, offset and length Words, then the zero-padded payload. -/
def calldataSize (payload : List UInt8) : Nat := 100 + paddedLength payload.length

/-- Original Core must complete every transaction with the prescribed
completion. A returned transaction adds its payload length to slot three,
leaves its last byte in slot four and returns the sum of the committed slots
zero, three and four plus its calldata size; a revert keeps the prior slots. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "bytes history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "bytes history length changed"
  let mut statuses : List String := []
  let mut prior ← history.getObjVal? "initialStorage"
  let mut total ← slotValue history "3" "initialStorage"
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "bytes history did not follow its flags parities"
    let committed ← row.getObjVal? "committedStorage"
    if status == "reverted" then
      unless committed == prior do throw "a reverted bytes transaction changed the committed slots"
    else
      let counted ← slotValue row "3"
      unless counted == (total + tx.payload.length) % 2 ^ 256 && (← slotValue row "4") == tailByte tx.payload do
        throw "a returned bytes transaction did not commit its length and last byte"
      let sum := ((← slotValue row "0") + counted + tailByte tx.payload + calldataSize tx.payload) % 2 ^ 256
      unless (← row.getObjValAs? String "output") == encodeBytesText (encodeWordBytesBE (Word.ofNatModulo sum)) do
        throw "a returned bytes transaction did not return its committed sum"
      total := counted
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "bytes history did not follow its prescribed flags parities"

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
            error == "bytes history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "bytes-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson bytesCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def payloadLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.payload.length) 0

/-- Flags and payload bytes all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.payload.foldl (fun sum byte => sum + byte.toNat) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the total payload
length, then flags and payload bytes. Every axis is a natural number and the
comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (payloadLength candidate < payloadLength source ∨
      (payloadLength candidate = payloadLength source ∧ valueWeight candidate < valueWeight source)))))

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

/-- Step reductions, then per transaction: removal, truncation of the payload
to each shorter bank length, zeroing its bytes, and flags reduced to their
parity or with the revert bit cleared. Candidates still need execution to
establish that they preserve a finding. -/
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
    for length in lengthBank.filter (· < transaction.payload.length) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with payload := tx.payload.take length})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with payload := List.replicate tx.payload.length 0})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
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
      ("functionVersion", Solcore.Synthesis.Core.DynamicBytes.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from bytes plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from bytes wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "bytes-generated" then
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
      throw "saved origin differs from generated bytes provenance"
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
  else throw "unsupported bytes case origin"
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
  return Json.mkObj [("schema", toJson bytesCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.DynamicBytes
end

section
-- leanmerge: from Solcore.Synthesis.Source.LongBytesEmitter
/-! Emit the fixed long-bytes protocol, the bytes profile's source with eight
chunk branches. The pinned ABI decoder produces `bytes` only in memory: it
follows the head offset, copies the length Word and up to eight payload Words
into fresh memory and zeroes the padding to a whole Word. The source therefore
reads chunk `k` as the zero-padded memory Word `mload(data + 32 + 32k)` and the
last payload byte through the unaligned Word that ends at it, whose low byte is
zero for an empty payload. The eight chunk branches, the slot writes and the
odd-flags revert follow the original Core contract in order. Memory at zero is
touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.LongBytes

open Solcore.Synthesis.Core.LongBytes (CheckedPlan chunkCount countSlot tailSlot)

def emitterVersion : String := "solcore-source-long-bytes-v2"
def wrapperVersion : String := "solcore-word-long-bytes-contract-v1"
def contractName : String := "SynthesizedLongBytes"
def methodName : String := "run"
def methodSignature : String := "run(uint256,bytes)"
def selector : String := "0x220eb9b6"
def deployPath : List String := ["SynthesizedLongBytesDeploy"]
def runtimePath : List String := ["SynthesizedLongBytesDeploy", "SynthesizedLongBytes"]

private def chunkLines (index : Nat) : List String :=
  ["        if (sc_length > " ++ toString (32 * index) ++ ") {",
    "            sc_acc = sc_step(sc_acc + mload(sc_data + " ++ toString (32 * (index + 1)) ++ "));",
    "            sstore(" ++ toString (index + 1) ++ ", sc_acc);",
    "        }"]

def emit (plan : CheckedPlan) : Except EmitError EmittedProgram := do
  let mut names : List String := []
  let mut lines := ["pragma solcore;", "import * from std;", "import * from std.dispatch;",
    AggregateRenderer.opcodeImportWith ["sload", "sstore", "mstore", "revert_", "mload", "calldatasize"]
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
    "    function " ++ methodName ++ "(flags: uint256, payload: memory<bytes>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_data: word = Typedef.rep(payload);",
    "        let sc_length: word = mload(sc_data);",
    "        let sc_acc: word = sload(0);"] ++ (List.range chunkCount).flatMap chunkLines ++ [
    "        let sc_tail: word = mload(sc_data + sc_length) & 255;",
    "        sstore(0, sc_acc);",
    "        let sc_total: word = sload(" ++ toString countSlot ++ ") + sc_length;",
    "        sstore(" ++ toString countSlot ++ ", sc_total);",
    "        sstore(" ++ toString tailSlot ++ ", sc_tail);",
    "        let sc_result: word = sload(0) + sload(" ++ toString countSlot ++ ") + sload(" ++ toString tailSlot ++
      ") + calldatasize();",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.LongBytes
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.LongBytesExecution
/-! Execute the original checked long-bytes contract over a persistent account
world. Each invocation starts a fresh Core heap and only the public terminal
`finalWorld` becomes the next transaction's world. Transactions and calldata are
the bytes profile's: the canonical ABI encoding of `(flags, payload)` with the
same selector, here with payloads of up to 256 bytes. Observations report the
eleven declared slots and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.LongBytesExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.LongBytes (CheckedPlan)
open Solcore.Synthesis.Stateful.DynamicBytesExecution (Transaction inputData?)

def historySchema : String := "solcore-lean.long-bytes-history.v2"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- Slot zero holds the accumulator, slots one to eight the per-chunk results,
slot nine the running byte count and slot ten the last payload byte. -/
def observedSlots : List Word := (List.range (Solcore.Synthesis.Core.LongBytes.tailSlot + 1)).map Word.ofNatModulo

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
      match inputData? transaction.flags transaction.payload, registry.resolve? prior bindings.address with
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.LongBytesExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.LongBytesCases
/-! Long-bytes cases retain one original host-aware Core contract and an
ordered history of `(flags, payload)` transactions, each payload of zero to 256
bytes in its canonical ABI encoding. Reductions remove transactions, truncate a
payload to a shorter bank length, zero its bytes or simplify flags. Saved
outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.LongBytes
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.LongBytes (CheckedPlan maxPayloadBytes guardNodes countSlot tailSlot)
open Solcore.Synthesis.Stateful.DynamicBytesExecution (Transaction paddedLength)
open Solcore.Synthesis.Stateful.LongBytesExecution (Bindings)
open Solcore.ContractRuntime (encodeBytesText decodeBytesText? encodeWordBytesBE)

def caseSchema : String := "solcore-lean.semantic-long-bytes-case.v1"
def planSchema : String := "solcore-lean.long-bytes-plan.v1"
def profileVersion : String := "stateful-long-bytes-v1/long-bytes-sequence-seed-v2"
def templateVersion : String := "bytes-eight-chunks-tail-size-revert-odd-flags-v1"
def longBytesCorpusSchema : String := "solcore-lean.semantic-long-bytes-corpus.v1"

/-- Payload lengths: empty, one byte, the bytes profile's bound, then both sides
of the third, fourth and fifth chunk boundaries, inside the seventh chunk, one
short of the bound and the bound. -/
def lengthBank : List Nat := [0, 1, 64, 65, 96, 97, 128, 129, 192, 223, 255, 256]

/-- Complete contracts may exceed the step budget by the fixed chunk guards. -/
def maxProgramNodes : Nat := 512 + guardNodes

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => tx.payload.length ≤ maxPayloadBytes) = true

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
    else throw "canonical long-bytes contract exceeds its case limit"
  else throw s!"long-bytes scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and payloads of at most 256 bytes"

def payloadText (payload : List UInt8) : String := encodeBytesText (ByteArray.mk payload.toArray)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("payload", toJson (payloadText tx.payload)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.DynamicBytesExecution.calldata tx.flags tx.payload)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let text ← row.getObjValAs? String "payload"
    unless text.length ≤ 2 + 2 * maxPayloadBytes do throw "payload exceeds 256 bytes"
    let some bytes := decodeBytesText? text | throw "payload is not canonical lowercase hexadecimal"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), bytes.data.toList⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, payload, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "long-bytes scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported long-bytes plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "long-bytes contract failed full host-Core admission"
  unless json == planJson plan do throw "long-bytes plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "long-bytes contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("longBytesPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.LongBytesExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.LongBytes.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic long-bytes case schema"
  let plan ← checkedPlan (← json.getObjVal? "longBytesPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical long-bytes plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.LongBytesExecution.slotsJson do
    throw "observed slots must be zero through ten"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.LongBytesExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three lengths, three byte patterns, then the completion pattern. Each
choice uses the high half of one draw from a separate stream: the low bits of a
power-of-two LCG have short periods. The stream starts at SplitMix64's finalizer
of the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def sequenceBounds : List Nat := [12, 12, 12, 4, 4, 4, 4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6c6f6e672d747874))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- 256 seeded bytes for each of three transactions from a further stream; each
draw contributes the four bytes of its high half. The stream starts at
SplitMix64's finalizer of the seed xor its domain, so that consecutive seeds'
bytes are not affine in the seed. -/
def seededPayloads (seed : Seed) : List (List UInt8) := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6c6f6e672d646174))
  let mut payloads : Array (List UInt8) := #[]
  for _ in List.range 3 do
    let mut bytes : Array UInt8 := #[]
    for _ in List.range 64 do
      let (value, next) := state.draw
      let high := value.toNat / 2 ^ 32
      bytes := bytes ++ #[(high / 2 ^ 24 % 256).toUInt8, (high / 2 ^ 16 % 256).toUInt8,
        (high / 2 ^ 8 % 256).toUInt8, (high % 256).toUInt8]
      state := next
    payloads := payloads.push bytes.toList
  return payloads.toList

/-- Zeros, `0xff`, the ramp `1, 2, 3, ...` or the seeded bytes, cut to `length`. -/
def patternBytes (pattern length : Nat) (seeded : List UInt8) : List UInt8 :=
  match pattern with
  | 0 => List.replicate length 0
  | 1 => List.replicate length 0xff
  | 2 => (List.range length).map fun position => (position + 1).toUInt8
  | _ => seeded.take length

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 6 0) [false, false, false]

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let seeded := seededPayloads seed
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityFlags odd,
      patternBytes (choices.getD (3 + index) 0) (lengthBank.getD (choices.getD index 0) 0) (seeded.getD index [])⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the fixed chunk guards lie outside the step budget, and the complete contract
is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.LongBytes.programOverhead < nodes do
    throw "node budget is too small for the long-bytes wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.LongBytes.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated long-bytes plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + guardNodes do
    throw "long-bytes contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "long-bytes-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : String) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some slot) |
    throw "committed slot missing"
  decimal entry "value"

/-- The last payload byte, or zero for an empty payload. -/
def tailByte (payload : List UInt8) : Nat := (payload.getLast?.map UInt8.toNat).getD 0

/-- Selector, flags, offset and length Words, then the zero-padded payload. -/
def calldataSize (payload : List UInt8) : Nat := 100 + paddedLength payload.length

/-- Original Core must complete every transaction with the prescribed
completion. A returned transaction adds its payload length to slot nine,
leaves its last byte in slot ten and returns the sum of the committed slots
zero, nine and ten plus its calldata size; a revert keeps the prior slots. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "long-bytes history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "long-bytes history length changed"
  let mut statuses : List String := []
  let mut prior ← history.getObjVal? "initialStorage"
  let mut total ← slotValue history (toString countSlot) "initialStorage"
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "long-bytes history did not follow its flags parities"
    let committed ← row.getObjVal? "committedStorage"
    if status == "reverted" then
      unless committed == prior do throw "a reverted long-bytes transaction changed the committed slots"
    else
      let counted ← slotValue row (toString countSlot)
      unless counted == (total + tx.payload.length) % 2 ^ 256 && (← slotValue row (toString tailSlot)) == tailByte tx.payload do
        throw "a returned long-bytes transaction did not commit its length and last byte"
      let sum := ((← slotValue row "0") + counted + tailByte tx.payload + calldataSize tx.payload) % 2 ^ 256
      unless (← row.getObjValAs? String "output") == encodeBytesText (encodeWordBytesBE (Word.ofNatModulo sum)) do
        throw "a returned long-bytes transaction did not return its committed sum"
      total := counted
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "long-bytes history did not follow its prescribed flags parities"

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
            error == "long-bytes history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "long-bytes-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson longBytesCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

def payloadLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.payload.length) 0

/-- Flags and payload bytes all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.payload.foldl (fun sum byte => sum + byte.toNat) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the total payload
length, then flags and payload bytes. Every axis is a natural number and the
comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (payloadLength candidate < payloadLength source ∨
      (payloadLength candidate = payloadLength source ∧ valueWeight candidate < valueWeight source)))))

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

/-- Step reductions, then per transaction: removal, truncation of the payload
to each shorter bank length, zeroing its bytes, and flags reduced to their
parity or with the revert bit cleared. Candidates still need execution to
establish that they preserve a finding. -/
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
    for length in lengthBank.filter (· < transaction.payload.length) do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with payload := tx.payload.take length})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with payload := List.replicate tx.payload.length 0})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
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
      ("functionVersion", Solcore.Synthesis.Core.LongBytes.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from long-bytes plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from long-bytes wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "long-bytes-generated" then
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
      throw "saved origin differs from generated long-bytes provenance"
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
  else throw "unsupported long-bytes case origin"
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
  return Json.mkObj [("schema", toJson longBytesCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.LongBytes
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedArrayEmitter
/-! Emit the fixed nested-array protocol. The ABI parameter is a lazily decoded
`calldata<array<calldata<array<uint256>>>>`, so `values.length()` reads the
same outer length Word as the Core contract, `values[uint256(i)]` follows row
`i`'s offset only inside the branch that the outer length admits, and the
row's `length()` and `row[uint256(j)]` read its length and elements the same
way. The three row branches with their two element branches, the slot writes,
the counter updates and the odd-flags revert follow the original Core contract
in order. Memory at zero is touched only before the terminal revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedArray

open Solcore.Synthesis.Core.NestedArray (CheckedPlan maxRows maxColumns rowSlot cellSlot)

def emitterVersion : String := "solcore-source-nested-array-v2"
def wrapperVersion : String := "solcore-word-nested-array-contract-v1"
def contractName : String := "SynthesizedNestedArray"
def methodName : String := "run"
def methodSignature : String := "run(uint256,uint256[][])"
def selector : String := "0x7095aff8"
def deployPath : List String := ["SynthesizedNestedArrayDeploy"]
def runtimePath : List String := ["SynthesizedNestedArrayDeploy", "SynthesizedNestedArray"]

private def cellLines (row column : Nat) : List String :=
  let i := toString row
  ["            if (sc_width" ++ i ++ " > " ++ toString column ++ ") {",
    "                sc_acc = sc_step(sc_acc + Typedef.rep(sc_row" ++ i ++ "[uint256(" ++ toString column ++ ")]));",
    "                sstore(" ++ toString (1 + maxColumns * row + column) ++ ", sc_acc);",
    "            }"]

private def rowLines (row : Nat) : List String :=
  let i := toString row
  ["        if (sc_rows > " ++ i ++ ") {",
    "            let sc_row" ++ i ++ ": calldata<array<uint256>> = values[uint256(" ++ i ++ ")];",
    "            let sc_width" ++ i ++ ": word = Typedef.rep(sc_row" ++ i ++ ".length());",
    "            sc_cells = sc_cells + sc_width" ++ i ++ ";"] ++
    (List.range maxColumns).flatMap (cellLines row) ++ ["        }"]

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
    "    function " ++ methodName ++
      "(flags: uint256, values: calldata<array<calldata<array<uint256>>>>) public returns (uint256) {",
    "        let sc_flags: word = Typedef.rep(flags);",
    "        let sc_rows: word = Typedef.rep(values.length());",
    "        let sc_cells: word = 0;",
    "        let sc_acc: word = sload(0);"] ++ (List.range maxRows).flatMap rowLines ++ [
    "        sstore(0, sc_acc);",
    "        sstore(" ++ toString rowSlot ++ ", sload(" ++ toString rowSlot ++ ") + sc_rows);",
    "        sstore(" ++ toString cellSlot ++ ", sload(" ++ toString cellSlot ++ ") + sc_cells);",
    "        let sc_result: word = sload(0) + sload(" ++ toString rowSlot ++ ") + sload(" ++ toString cellSlot ++ ");",
    "        if ((sc_flags & 1) == 1) {",
    "            mstore(0, sc_result);",
    "            revert_(0, 32);",
    "        }",
    "        return uint256(sc_result);", "    }", "}"]
  return {
    source := String.intercalate "\n" lines ++ "\n"
    contractName, methodName, methodSignature, deployPath, runtimePath
  }

end Solcore.Synthesis.Source.NestedArray
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.NestedArrayExecution
/-! Execute the original checked nested-array contract over a persistent
account world. Each invocation starts a fresh Core heap and only the public
terminal `finalWorld` becomes the next transaction's world. Calldata is the
canonical ABI encoding of `(flags, values)` for `uint256[][]`: the static head,
the outer offset 64, the outer length, one offset per row measured from the
start of that offset table, then each row's length and elements. Observations
report the nine declared slots and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.NestedArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.NestedArray (CheckedPlan)

def historySchema : String := "solcore-lean.nested-array-history.v2"

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
  let initialWhole := AccountStorage.contractJson world bindings.address
  let mut rows : Array Json := #[]
  let mut stopped : Option String := none
  for (transaction, index) in transactions.zipIdx do
    if stopped.isNone then
      let prior := world
      let common := [("id", toJson transaction.id), ("index", toJson index)]
      match inputData? transaction.flags transaction.values, registry.resolve? prior bindings.address with
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

def observe (plan : CheckedPlan) (transactions : List Transaction)
    (bindings : Bindings) (fuel : Nat) : Json :=
  observeContract plan.contract transactions bindings fuel

end Solcore.Synthesis.Stateful.NestedArrayExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.NestedArrayCases
/-! Nested-array cases retain one original host-aware Core contract and an
ordered history of `(flags, values)` transactions, each value of at most three
rows of at most two elements in its canonical nested ABI encoding. Reductions
remove transactions, rows or a row's last element and simplify flags or
elements. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.NestedArray
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.Synthesis.Core.NestedArray (CheckedPlan maxRows maxColumns guardNodes rowSlot cellSlot)
open Solcore.Synthesis.Stateful.NestedArrayExecution (Transaction Bindings)
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)

def caseSchema : String := "solcore-lean.semantic-nested-array-case.v1"
def planSchema : String := "solcore-lean.nested-array-plan.v1"
def profileVersion : String := "stateful-nested-array-v1/nested-array-sequence-seed-v2"
def templateVersion : String := "nested-fold-slots-counts-revert-odd-flags-v1"
def nestedCorpusSchema : String := "solcore-lean.semantic-nested-array-corpus.v1"

/-- Element values; the bank of the two-slot storage profiles. -/
abbrev boundaryInputs := Storage.boundaryInputs

/-- Complete contracts may exceed the step budget by the fixed row and element guards. -/
def maxProgramNodes : Nat := 512 + guardNodes

def validValue (values : List (List Word)) : Bool :=
  values.length ≤ maxRows && values.all (·.length ≤ maxColumns)

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all (fun tx => Storage.validId tx.id) = true ∧
    transactions.all (fun tx => validValue tx.values) = true

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
    else throw "canonical nested-array contract exceeds its case limit"
  else throw s!"nested-array scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs and at most three rows of two elements each"

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun row => row.map fun value => toString value.val)),
  ("calldata", toJson (Solcore.Synthesis.Stateful.NestedArrayExecution.calldata tx.flags tx.values)),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List (List String)) "values"
    unless texts.length ≤ maxRows && texts.all (·.length ≤ maxColumns) do
      throw "value exceeds three rows of two elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM (·.mapM word)⟩
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, calldata or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "nested-array scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported nested-array plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "nested-array contract failed full host-Core admission"
  unless json == planJson plan do throw "nested-array plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "nested-array contract exceeds its case limit"
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
    ("schema", toJson caseSchema), ("nestedArrayPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.NestedArrayExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.NestedArray.version),
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
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic nested-array case schema"
  let plan ← checkedPlan (← json.getObjVal? "nestedArrayPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical nested-array plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.NestedArrayExecution.slotsJson do
    throw "observed slots must be zero through eight"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.NestedArrayExecution.observe scenario.plan scenario.transactions bindings fuel

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

def parityFlags (odd : Bool) : Word := if odd then Word.ofNatModulo 1 else Word.zero

/-- Revert positions of the four generated completion patterns. -/
def parityPatterns : List (List Bool) :=
  [[false, false, false], [false, true, false], [true, false, false], [false, false, true]]

/-- Three outer lengths, three row lengths per transaction, two elements per
row, then the completion pattern. Each choice uses the high half of one draw
from a separate stream: the low bits of a power-of-two LCG have short periods.
The stream starts at SplitMix64's finalizer of the seed xor its domain, so that
consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := [4, 4, 4] ++ List.replicate 9 3 ++ List.replicate 18 6 ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6e6573742d617272))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def generatedParities (seed : Seed) : List Bool :=
  parityPatterns.getD ((sequenceChoices seed).getD 30 0) [false, false, false]

/-- Transaction `i` has `choices[i]` rows; row `r` has `choices[3 + 3i + r]`
elements, element `c` drawn by `choices[12 + 6i + 2r + c]`. -/
def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  (generatedParities seed).zipIdx.map fun (odd, index) =>
    ⟨"tx-" ++ toString (first + index), parityFlags odd,
      (List.range (choices.getD index 0)).map fun row =>
        (List.range (choices.getD (3 + 3 * index + row) 0)).map fun column =>
          bank (12 + 6 * index + 2 * row + column)⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- Reserve the measured host wrapper before generating its independent step;
the fixed row and element guards lie outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.NestedArray.programOverhead < nodes do
    throw "node budget is too small for the nested-array wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.NestedArray.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated nested-array plan failed full Core admission"
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + guardNodes do
    throw "nested-array contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "nested-array-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("sequenceCompletions", toJson ((Stateful.Sequence.blocks (fun blockSeed _ => generatedParities blockSeed) seed
      transactions).map statusName))]) transactions)

private def decimal (row : Json) (key : String) : Except String Nat := do
  let some value := (← row.getObjValAs? String key).toNat? | throw ("invalid " ++ key)
  return value

private def slotValue (row : Json) (slot : Nat) (field : String := "committedStorage") : Except String Nat := do
  let rows ← row.getObjValAs? (List Json) field
  let some entry := rows.find? (fun entry => (entry.getObjValAs? String "slot").toOption == some (toString slot)) |
    throw "committed slot missing"
  decimal entry "value"

def elementCount (tx : Transaction) : Nat := tx.values.foldl (fun total row => total + row.length) 0

/-- Original Core must complete every transaction with the prescribed
completion and a one-Word payload. A returned transaction adds its row count to
slot seven and its element count to slot eight and returns the sum of the
committed slots zero, seven and eight; a revert keeps the prior slots. -/
def checkProtocol (scenario : CheckedScenario) (history : Json) : Except String (List String) := do
  unless (← history.getObjValAs? String "status") = "complete" do
    throw "nested-array history exhausted Core fuel"
  let rows ← history.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "nested-array history length changed"
  let mut statuses : List String := []
  let mut prior ← history.getObjVal? "initialStorage"
  let mut rowTotal ← slotValue history rowSlot "initialStorage"
  let mut cellTotal ← slotValue history cellSlot "initialStorage"
  for (row, tx) in rows.zip scenario.transactions do
    let status ← row.getObjValAs? String "status"
    unless status == statusName (reverts tx) do throw "nested-array history did not follow its flags parities"
    unless (← row.getObjValAs? String "output").length == 66 do throw "a nested-array payload is not one Word"
    let committed ← row.getObjVal? "committedStorage"
    if status == "reverted" then
      unless committed == prior do throw "a reverted nested-array transaction changed the committed slots"
    else
      let rowsNow ← slotValue row rowSlot
      let cellsNow ← slotValue row cellSlot
      unless rowsNow == (rowTotal + tx.values.length) % 2 ^ 256 && cellsNow == (cellTotal + elementCount tx) % 2 ^ 256 do
        throw "a returned nested-array transaction did not commit its row and element counts"
      let sum := ((← slotValue row 0) + rowsNow + cellsNow) % 2 ^ 256
      unless (← row.getObjValAs? String "output") == encodeBytesText (encodeWordBytesBE (Word.ofNatModulo sum)) do
        throw "a returned nested-array transaction did not return its committed sum"
      rowTotal := rowsNow
      cellTotal := cellsNow
    prior := committed
    statuses := statuses ++ [status]
  return statuses

def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  let statuses ← checkProtocol scenario observed
  unless statuses == scenario.transactions.map (fun tx => statusName (reverts tx)) do
    throw "nested-array history did not follow its prescribed flags parities"

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
            error == "nested-array history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "nested-array-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson nestedCorpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- Every row and every element counts once. -/
def shapeSize (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => sum + 1 + row.length) total) 0

/-- Flags and elements all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => row.foldl (fun inner value => inner + value.val) sum)
      (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the total number of
rows and elements, then flags and elements. Every axis is a natural number and
the comparison is lexicographic. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (shapeSize candidate < shapeSize source ∨
      (shapeSize candidate = shapeSize source ∧ valueWeight candidate < valueWeight source)))))

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

private def dropLastOf (values : List (List Word)) (row : Nat) : List (List Word) :=
  values.zipIdx.map fun (cells, current) => if current == row then cells.dropLast else cells

/-- Step reductions, then per transaction: removal, removal of each row,
removal of each nonempty row's last element, zeroing every element, and flags
reduced to their parity or with the revert bit cleared. Candidates still need
execution to establish that they preserve a finding. -/
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
    for row in List.range transaction.values.length do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with values := tx.values.eraseIdx row})]
    for (cells, row) in transaction.values.zipIdx do
      if !cells.isEmpty then
        raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
          {tx with values := dropLastOf tx.values row})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with values := tx.values.map fun cells => cells.map fun _ => Word.zero})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1)})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with flags := tx.flags.bitAnd (Word.ofNatModulo 1).bitNot})]
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
      ("functionVersion", Solcore.Synthesis.Core.NestedArray.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← (emit admitted.plan).mapError reprStr
  unless (← json.getObjValAs? String "source") = emitted.source do throw "saved source differs from nested-array plan emission"
  unless (← json.getObjVal? "contract") == contractJson emitted do throw "saved contract metadata differs from nested-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "nested-array-generated" then
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
      throw "saved origin differs from generated nested-array provenance"
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
  else throw "unsupported nested-array case origin"
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
  return Json.mkObj [("schema", toJson nestedCorpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.NestedArray
end
