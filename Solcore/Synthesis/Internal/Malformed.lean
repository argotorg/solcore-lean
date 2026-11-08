import Solcore.Synthesis.Internal.Aggregates
import Solcore.Synthesis.Internal.AbiValues
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.Core.Wire.Codec
import Solcore.Synthesis.Stateful.Sequence
import Solcore.Synthesis.Internal.Storage

/-!
# Profiles: malformed calldata

The profiles `stateful-malformed-calldata`, `stateful-malformed-bytes` and
`stateful-malformed-nested-array`.
-/

section
-- leanmerge: from Solcore.Synthesis.Core.MalformedBytes
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
end

section
-- leanmerge: from Solcore.Synthesis.Core.MalformedCalldata
/-! The dynamic-array protocol behind the pinned std's dispatcher and decoder
for `run(uint256 flags, uint256[] values)`. Before the protocol runs, the
contract evaluates std's checks on the actual calldata in std's order, through
the exact input host functions: calldata shorter than four bytes or with
another selector reaches the default fallback (`0x4924aef0`); a head shorter
than 64 bytes, a head offset, length word or element region outside the
calldata, or a length whose 32-fold product would wrap reverts with
`ABIInputTruncated` (`0x08638556`). Overlapping offsets and trailing bytes are
not checked. A rejection reverts with the error selector as its Word payload,
which the comparison relates to std's four-byte revert data. The protocol is
the dynamic-array one: at most three decoded elements fold through a closed
aggregate step, element `i` writing slot `1 + i`; slot zero holds the
accumulator and slot four the running length, and odd flags revert. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MalformedCalldata

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-malformed-calldata-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The selector of `run(uint256,uint256[])`. -/
def selector : Nat := 0x9a94c44b

/-- std's `NoSelectorMatchedWithoutFallback()`, reverted by the default fallback. -/
def noSelectorError : Nat := 0x4924aef0

/-- std's `ABIInputTruncated()`, reverted by every bounded calldata read. -/
def truncatedError : Nat := 0x08638556

/-- The std rejections this contract produces. An index past a length, std's
`Panic(0x32)`, cannot arise, since the protocol guards every index by the length, and the non-payable
check cannot fail, since no transaction carries value. -/
def stdErrors : List Nat := [noSelectorError, truncatedError]

/-- The largest length std admits for 32-byte elements, `~0 / 32`. -/
def maxLength : Nat := 2 ^ 251 - 1

/-- Elements beyond this bound are never read by the protocol. -/
def maxElements : Nat := 3

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def gt (left right : Expr) : Expr := .binary .wordGt left right
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def sub (left right : Expr) : Expr := .binary .wordSub left right
private def mul (left right : Expr) : Expr := .binary .wordMul left right

/-- A complete calldata Word; every read happens after the checks that make
its window present, so the zero branch is unreachable. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- One calldata byte, read only once the size admits it. -/
private def byteAt (locals offset : Nat) : Expr :=
  .caseE (host 6 locals (word offset)) (word 0) (.var 0)

/-- The first four calldata bytes as a big-endian number. -/
private def selectorWord (locals : Nat) : Expr :=
  add (add (add (mul (byteAt locals 0) (word (2 ^ 24))) (mul (byteAt locals 1) (word (2 ^ 16))))
    (mul (byteAt locals 2) (word (2 ^ 8)))) (byteAt locals 3)

/-- A std rejection: revert with the error selector as the Word payload. -/
private def reject (error : Nat) : Expr := .inRight .word (.inLeft .word (word error))

/-- Element `index` in a frame with `locals` binders, where the newest
accumulator is local zero, the length is local `index + 1`, the head offset
local `index + 2`, the flags `index + 3`, the size `index + 4` and the step
`index + 5`. The element Word lies `36 + offset + 32 * index` bytes in. -/
private def element (index locals : Nat) : Expr :=
  .ifE (gt (.var (index + 1)) (word index))
    (.letE (readAt locals (add (add (word 36) (.var (index + 2))) (word (32 * index))))
      (.letE (.apply (.var (index + 6)) (add (.var 1) (.var 0)))
        (.letE (host 1 (locals + 2) (.pair (word (index + 1)) (.var 0)))
          (.var 1))))
    (.var 0)

/-- After the result binding, the flags are local ten. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- The dynamic-array protocol over the decoded length (local zero), head
offset, flags, size and step. -/
private def protocol : Expr :=
  .letE (host 0 5 (word 0))
    (.letE (element 0 6)
      (.letE (element 1 7)
        (.letE (element 2 8)
          (.letE (host 1 9 (.pair (word 0) (.var 0)))
            (.letE (add (host 0 10 (word 4)) (.var 5))
              (.letE (host 1 11 (.pair (word 4) (.var 0)))
                (.letE (add (host 0 12 (word 0)) (host 0 12 (word 4)))
                  completion)))))))

/-- std's dispatch and decoding in its order, then the protocol. With the size
bound, the offset `o` (local zero after its binding) satisfies `o <= size - 4`
before `4 + o` is formed, and the length satisfies `length <= ~0 / 32` before
`32 * length` is formed, so no checked arithmetic wraps. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (host 7 1 .unit)
      (.ifE (gt (word 4) (.var 0)) (reject noSelectorError)
        (.ifE (.binary .wordEq (selectorWord 2) (word selector))
          (.ifE (gt (word 68) (.var 0)) (reject truncatedError)
            (.letE (readAt 2 (word 4))
              (.letE (readAt 3 (word 36))
                (.ifE (gt (.var 0) (sub (.var 2) (word 4))) (reject truncatedError)
                  (.ifE (gt (word 32) (sub (.var 2) (add (word 4) (.var 0)))) (reject truncatedError)
                    (.letE (readAt 4 (add (word 4) (.var 0)))
                      (.ifE (gt (.var 0) (word maxLength)) (reject truncatedError)
                        (.ifE (gt (mul (.var 0) (word 32)) (sub (.var 3) (add (word 36) (.var 1))))
                          (reject truncatedError)
                          protocol))))))))
          (reject noSelectorError))))

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
end Solcore.Synthesis.Core.MalformedCalldata
end

section
-- leanmerge: from Solcore.Synthesis.Core.MalformedNestedArray
/-! The nested-array protocol behind the pinned std's dispatcher and lazy
decoder for `run(uint256 flags, uint256[][] values)`. The contract first
evaluates std's dispatch and outer array checks on the actual calldata: the
outer length must not exceed `~0 / 32` and its whole offset table, which starts
at `T = 36 + o`, must fit. Then it runs the nested-array protocol, and each row
the protocol reads is decoded by std's checks at that point: row `i`'s table
Word `r` must satisfy `r <= size - T`, 32 bytes must remain at `T + r`, and the
row length must not exceed `~0 / 32` and its elements must fit. Rows the
protocol never reads are never checked, and overlaps and trailing bytes are not
checked. A rejection reverts with the error selector as its Word payload. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.MalformedNestedArray

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.StdDispatch

def version : String := "core-malformed-nested-array-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The selector of `run(uint256,uint256[][])`. -/
def selector : Nat := 0x7095aff8

/-- The std rejections this contract produces. An index past a length, std's
`Panic(0x32)`, cannot arise, since the protocol guards every row index by the outer length and every
element index by the row length, and the non-payable check cannot fail, since
no transaction carries value. -/
def stdErrors : List Nat := [noSelectorError, truncatedError]

/-- Rows and elements per row that the protocol reads. -/
abbrev readRows : Nat := NestedArray.maxRows
abbrev readColumns : Nat := NestedArray.maxColumns

/-- The binder at position `position`, counted from the outermost, seen from a
frame of `locals` binders. -/
private def binder (locals position : Nat) : Expr := .var (locals - 1 - position)

/- Binder positions: the step 0, the size 1, the flags 2, the head offset 3,
the outer length 4 and the initial accumulator 5. Row `i` then binds its start
`6 + bi`, its length `7 + bi` and its elements' accumulators `8 + bi + j`,
where `b` is `readColumns + 2`. -/
private def block : Nat := readColumns + 2
private def rowStart (row : Nat) : Nat := 6 + block * row
private def rowLength (row : Nat) : Nat := 7 + block * row
private def cellAcc (row column : Nat) : Nat := 8 + block * row + column
/-- The accumulator before element `(i, j)`: the previous element's, or the
initial one before row zero. -/
private def accBefore (row column : Nat) : Nat :=
  if column = 0 then 5 + block * row else cellAcc row (column - 1)

private def size (locals : Nat) : Expr := binder locals 1
private def outerLength (locals : Nat) : Expr := binder locals 4
/-- The start of the offset table, past the outer length Word at `4 + o`. -/
private def table (locals : Nat) : Expr := add (binder locals 3) (word 36)

/-- std's decode of row `row` when the outer length admits it: true when it
reverts. The table Word `r` is compared with `size - T` before `T + r` is
formed, and the row length `m` with `~0 / 32` before `32 * m`. -/
private def rowRejected (row locals : Nat) : Expr :=
  .ifE (gt (outerLength locals) (word row))
    (.letE (readAt locals (add (table locals) (word (32 * row))))
      (.ifE (gt (.var 0) (sub (size (locals + 1)) (table (locals + 1)))) (.bool true)
        (.ifE (gt (word 32) (sub (size (locals + 1)) (add (table (locals + 1)) (.var 0)))) (.bool true)
          (.letE (readAt (locals + 1) (add (table (locals + 1)) (.var 0)))
            (.ifE (gt (.var 0) (word maxLength)) (.bool true)
              (gt (mul (.var 0) (word 32))
                (sub (size (locals + 2)) (add (add (table (locals + 2)) (.var 1)) (word 32)))))))))
    (.bool false)

/-- The absolute byte position of row `i`'s length Word: the table start plus
the row's table Word. -/
private def startOf (row : Nat) (locals : Nat) : Expr :=
  .ifE (gt (outerLength locals) (word row))
    (add (table locals) (readAt locals (add (table locals) (word (32 * row)))))
    (word 0)

private def lengthOf (row : Nat) (locals : Nat) : Expr :=
  .ifE (gt (outerLength locals) (word row)) (readAt locals (binder locals (rowStart row))) (word 0)

/-- Element `(i, j)`, present when the row's length exceeds `j`: fold it through
the step and write its slot; otherwise keep the accumulator. -/
private def cell (row column : Nat) (locals : Nat) : Expr :=
  .ifE (gt (binder locals (rowLength row)) (word column))
    (.letE (readAt locals (add (binder locals (rowStart row)) (word (32 + 32 * column))))
      (.letE (.apply (binder (locals + 1) 0) (add (binder (locals + 1) (accBefore row column)) (.var 0)))
        (.letE (host 1 (locals + 2) (.pair (word (1 + readColumns * row + column)) (.var 0)))
          (.var 1))))
    (binder locals (accBefore row column))

/-- Each row's std check, start, length and elements in turn, then `finish`. -/
private def rowsFrom (rows : Nat) (finish : Nat → Expr) : Nat → Nat → Expr
  | 0, _ => finish rows
  | remaining + 1, row =>
      let locals := rowStart row
      .ifE (rowRejected row locals) (reject truncatedError)
        (.letE (startOf row locals)
          (.letE (lengthOf row (locals + 1))
            ((List.range readColumns).foldr
              (fun column body => .letE (cell row column (locals + 2 + column)) body)
              (rowsFrom rows finish remaining (row + 1)))))

/-- After `rows` rows: the element count, the slot writes, the rereads and the
completion. -/
private def finish (rows : Nat) : Expr :=
  let locals := 6 + block * rows
  let cells := (List.range rows).foldl (fun total row => add total (binder locals (rowLength row))) (word 0)
  .letE cells
    (.letE (host 1 (locals + 1) (.pair (word 0) (binder (locals + 1) (5 + block * rows))))
      (.letE (host 1 (locals + 2) (.pair (word (1 + readColumns * rows))
          (add (host 0 (locals + 2) (word (1 + readColumns * rows))) (binder (locals + 2) 4))))
        (.letE (host 1 (locals + 3) (.pair (word (2 + readColumns * rows))
            (add (host 0 (locals + 3) (word (2 + readColumns * rows))) (binder (locals + 3) locals))))
          (.letE (add (add (host 0 (locals + 4) (word 0)) (host 0 (locals + 4) (word (1 + readColumns * rows))))
              (host 0 (locals + 4) (word (2 + readColumns * rows))))
            (.ifE (.binary .wordEq (.binary .wordAnd (binder (locals + 5) 2) (word 1)) (word 1))
              (.inRight .word (.inLeft .word (.var 0)))
              (.inLeft (.sum .word .word) (.var 0)))))))

/-- std's dispatch, head and outer array checks in its order, then the rows.
The outer length `n` (local zero after its binding) satisfies `n <= ~0 / 32`
before `32 * n` is formed. -/
private def contractExpressionWith (rows : Nat) (stepBody : Expr) : Expr :=
  dynamicHead selector stepBody
    (.letE (readAt 4 (add (word 4) (.var 0)))
      (.ifE (gt (.var 0) (word maxLength)) (reject truncatedError)
        (.ifE (gt (mul (.var 0) (word 32)) (sub (.var 3) (add (word 36) (.var 1)))) (reject truncatedError)
          (.letE (host 0 5 (word 0))
            (rowsFrom rows finish rows 0)))))

private def contractExpression (stepBody : Expr) : Expr := contractExpressionWith readRows stepBody

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead with `rows` row checks and guards; the placeholder is
never admitted or run. -/
private def overheadWith (rows : Nat) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpressionWith rows (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The fixed row checks and guards' size, which lies outside the step's node budget. -/
def guardNodes : Nat := overheadWith readRows - overheadWith 0

/-- The std checks and protocol wrapper around the step without the rows. -/
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
end Solcore.Synthesis.Core.MalformedNestedArray
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.MalformedBytesExecution
/-! Execute the original checked malformed-bytes contract over a persistent
account world. A transaction is a canonical `(flags, payload)` call of
`run(uint256,bytes)`, with a payload of at most 256 bytes, together with one
malformation of its calldata; the contract receives the malformed bytes.
`stdDecode` is a second model of the pinned std's dispatcher and `bytes`
decoder, written over the bytes instead of in Core, which prescribes each
transaction's outcome and the payload the body reads. Observations report
slots zero to ten and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedBytesExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedBytes (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-bytes-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- How a transaction's calldata departs from the canonical encoding of its
flags and payload: the malformed-calldata kinds, with `length` replacing the
payload length Word, or nonzero padding after a payload that does not fill its
last Word. Padding patterns are `0xff` (0), the ramp `1, 2, 3, ...` (1) or a
single `0x01` in the last padding byte (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | padding (pattern : Nat)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  payload : List UInt8
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  DynamicBytesExecution.inputBytes tx.flags tx.payload

/-- The payload starts after the selector, the flags, the tail offset 64 and
the length Word. -/
def payloadStart : Nat := 100

/-- The padding bytes after a payload of `length` bytes. -/
def paddingCount (length : Nat) : Nat := DynamicBytesExecution.paddedLength length - length

/-- The last payload Word with its padding replaced by the pattern. -/
private def paddedWord (payload : List UInt8) (pattern : Nat) : Word :=
  let start := payload.length / 32 * 32
  let count := paddingCount payload.length
  let padding := (List.range count).map fun position =>
    match pattern with
    | 0 => (0xff : UInt8)
    | 1 => (position + 1).toUInt8
    | _ => if position + 1 = count then 1 else 0
  Word.ofNatModulo ((payload.drop start ++ padding).foldl (fun total byte => total * 256 + byte.toNat) 0)

def Malformation.change (payload : List UInt8) : Malformation → StdCalldata.Change
  | .none => .none
  | .short bytes => .short bytes
  | .selector mask => .selector mask
  | .truncate kept => .truncate kept
  | .trailing count pattern => .trailing count pattern
  | .offset value => .word 36 value
  | .length value => .word 68 value
  | .padding pattern => .word (payloadStart + payload.length / 32 * 32) (paddedWord payload pattern)

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (tx.malformation.change tx.payload).apply (canonicalBytes tx)

/-- A malformation within its bounds; padding needs a payload that does not
fill its last Word, and one of the three patterns. -/
def Malformation.valid (malformation : Malformation) (payload : List UInt8) (canonicalSize : Nat) : Bool :=
  (match malformation with
    | .padding pattern => pattern < 3 && paddingCount payload.length != 0
    | _ => true) &&
  (malformation.change payload).valid canonicalSize

/-- The pinned std's decision for `run(uint256,bytes)` over raw calldata, with
the flags and the payload it copies into memory: after the dispatch and head
checks, the payload length must not exceed the bytes after its length Word,
and then std's bound `length <= ~0 - 63` holds. The padding is neither
required nor read. Otherwise the rejecting error selector. -/
def stdDecode (input : ByteArray) : Except Nat (Nat × List UInt8) := do
  let (flags, offset) ← StdCalldata.dynamicHead? input Solcore.Synthesis.Core.MalformedBytes.selector
  let length := StdCalldata.wordAt input (4 + offset)
  if length > input.size - (36 + offset) then throw Solcore.Synthesis.Core.StdDispatch.truncatedError
  if length > Solcore.Synthesis.Core.MalformedBytes.maxPayloadLength then
    throw Solcore.Synthesis.Core.StdDispatch.truncatedError
  return (flags, (input.extract (36 + offset) (36 + offset + length)).data.toList)

def stdRejection? (input : ByteArray) : Option Nat :=
  match stdDecode input with
  | .error selector => some selector
  | .ok _ => none

def stdDecoded? (input : ByteArray) : Option (Nat × List UInt8) := (stdDecode input).toOption

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := LongBytesExecution.observedSlots
abbrev slotsJson := LongBytesExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => LongBytesExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the long-bytes profile,
with each transaction's malformed calldata as the input. -/
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
      match inputData? transaction, registry.resolve? prior bindings.address with
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

end Solcore.Synthesis.Stateful.MalformedBytesExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.MalformedBytesCases
/-! Malformed-bytes cases retain the std-modeling original Core contract
around a checked aggregate step and an ordered history of long-bytes calls,
each with one malformation of its calldata. The compiled contract is the
long-bytes one, emitted from the same step. Every transaction records its
malformation, the calldata it sends and the outcome std prescribes for those
bytes. Reductions remove transactions, simplify the step, drop or simplify a
malformation, and then shorten payloads and reduce flags. Saved outputs are
never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MalformedBytes
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE decodeBytesText?)
open Solcore.Synthesis.Core.MalformedBytes (CheckedPlan guardNodes)
open Solcore.Synthesis.Stateful.MalformedBytesExecution
  (Malformation Transaction Bindings stdRejection? payloadStart paddingCount)

def caseSchema : String := "solcore-lean.semantic-malformed-bytes-case.v1"
def planSchema : String := "solcore-lean.malformed-bytes-plan.v1"
def profileVersion : String := "stateful-malformed-bytes-v1/malformation-sequence-seed-v2"
def templateVersion : String := "std-dispatch-bytes-eight-chunks-tail-size-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-malformed-bytes-corpus.v1"

abbrev emitterVersion := LongBytes.emitterVersion
abbrev wrapperVersion := LongBytes.wrapperVersion
abbrev lengthBank := LongBytes.lengthBank

/-- Complete contracts may exceed the step budget by the fixed chunk guards. -/
def maxProgramNodes : Nat := 512 + guardNodes

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "offset", "length", "padding"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .padding _ => "padding"

abbrev patternNames := Stateful.StdCalldata.patternNames
def paddingNames : List String := ["ones", "ramp", "last-byte"]

def canonicalSize (tx : Transaction) : Nat :=
  (Solcore.Synthesis.Stateful.MalformedBytesExecution.canonicalBytes tx).size

def validTransaction (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.payload.length ≤ Solcore.Synthesis.Core.LongBytes.maxPayloadBytes &&
    tx.malformation.valid tx.payload (canonicalSize tx) &&
    (Solcore.Synthesis.Stateful.MalformedBytesExecution.inputBytes tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all validTransaction = true

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
    else throw "canonical malformed-bytes contract exceeds its case limit"
  else throw s!"malformed-bytes scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, payloads of at most 256 bytes and a valid malformation of at most 1 KiB each"

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .padding pattern => Json.mkObj [("kind", toJson "padding"), ("pattern", toJson (paddingNames.getD pattern "last-byte"))]

abbrev selectorText := Stateful.StdCalldata.selectorText

def prescribed (tx : Transaction) : Option Nat :=
  stdRejection? (Solcore.Synthesis.Stateful.MalformedBytesExecution.inputBytes tx)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("payload", toJson (LongBytes.payloadText tx.payload)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MalformedBytesExecution.calldata tx)),
  ("stdRejection", match prescribed tx with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value ≤ 2 ^ 32 do throw ("malformation " ++ key ++ " is out of range")
  return value

def decodeMalformation (json : Json) : Except String Malformation := do
  let kind ← json.getObjValAs? String "kind"
  if kind = "none" then return .none
  else if kind = "short" then return .short (← natural json "bytes")
  else if kind = "selector" then
    let text ← json.getObjValAs? String "mask"
    unless text.length ≤ 10 do throw "selector mask exceeds 32 bits"
    let some mask := text.toNat? | throw "invalid selector mask"
    return .selector mask
  else if kind = "truncate" then return .truncate (← natural json "kept")
  else if kind = "trailing" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := patternNames.idxOf? name | throw "unknown trailing pattern"
    return .trailing (← natural json "count") pattern
  else if kind = "offset" then return .offset (← word (← json.getObjValAs? String "value"))
  else if kind = "length" then return .length (← word (← json.getObjValAs? String "value"))
  else if kind = "padding" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := paddingNames.idxOf? name | throw "unknown padding pattern"
    return .padding pattern
  else throw "unknown malformation kind"

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let text ← row.getObjValAs? String "payload"
    unless text.length ≤ 2 + 2 * Solcore.Synthesis.Core.LongBytes.maxPayloadBytes do throw "payload exceeds 256 bytes"
    let some bytes := decodeBytesText? text | throw "payload is not canonical lowercase hexadecimal"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), bytes.data.toList,
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransaction transaction do throw "invalid transaction ID, payload or malformation"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, payload, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "malformed-bytes scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

/-- The long-bytes plan of the same step, whose source is the compiled contract. -/
def bytesPlan (plan : CheckedPlan) : Except String Solcore.Synthesis.Core.LongBytes.CheckedPlan := do
  let some bytesPlan := Solcore.Synthesis.Core.LongBytes.CheckedPlan.ofStep? plan.step |
    throw "the step fails the long-bytes contract's admission"
  return bytesPlan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported malformed-bytes plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "malformed-bytes contract failed full host-Core admission"
  unless json == planJson plan do throw "malformed-bytes plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "malformed-bytes contract exceeds its case limit"
  let _ ← bytesPlan plan
  return plan

def emit (plan : CheckedPlan) : Except String EmittedProgram := do
  (LongBytes.emit (← bytesPlan plan)).mapError reprStr

abbrev contractJson := LongBytes.contractJson
abbrev initialStateJson := LongBytes.initialStateJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("malformedBytesPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MalformedBytesExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.MalformedBytes.version),
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
  let emitted ← emit scenario.plan
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic malformed-bytes case schema"
  let plan ← checkedPlan (← json.getObjVal? "malformedBytesPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical malformed-bytes plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MalformedBytesExecution.slotsJson do
    throw "observed slots must be zero through ten"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MalformedBytesExecution.observe scenario.plan scenario.transactions bindings fuel

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The malformations a transaction with a payload of `length` bytes and
canonical size `size` draws from, by kind: none; short calldata; wrong
selectors; cuts in the head, the length Word, the last payload byte, the
padding and the last Word; trailing bytes; out-of-range, wrapping and
overlapping head offsets; one too long, the most that fits, one more than
fits, above `~0 - 63`, maximal, shorter and zero lengths; and nonzero padding.
Changes that leave the canonical calldata as it is and cuts outside it are left
out. -/
def malformationBank (length size : Nat) : List (List Malformation) :=
  let fits := size - payloadStart
  let cuts := ([4, 36, 67, 99] ++ (if length = 0 then [] else [payloadStart + length - 1]) ++
      (if paddingCount length = 0 then [] else [payloadStart + length]) ++ [size - 32, size - 1]).eraseDups.filter
    fun kept => 4 ≤ kept && kept < size
  [[.none],
    [.short 0, .short 1, .short 2, .short 3],
    [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)],
    cuts.map .truncate,
    [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2],
    [size - 3, size - 35, 2 ^ 255, 2 ^ 256 - 4, 2 ^ 256 - 2, 2 ^ 256 - 1, 0, 32].map (.offset ∘ w),
    ([length + 1, fits, fits + 1, Solcore.Synthesis.Core.MalformedBytes.maxPayloadLength + 1, 2 ^ 256 - 1,
      2 ^ 255, length - 1, 0].eraseDups.filter (· != length)).map (.length ∘ w),
    if paddingCount length = 0 then [] else [.padding 0, .padding 1, .padding 2]]

/-- A kind and a parameter for each of three transactions, each the high half of
one draw from a separate stream. The stream starts at SplitMix64's finalizer of
the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def malformationChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x62797465732d6d61))
  let mut values : Array Nat := #[]
  for bound in [8, 8, 8, 8, 8, 8] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- The long-bytes block, each transaction with a malformation drawn from its bank. -/
def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := malformationChoices seed
  (LongBytes.blockTransactions seed first).zipIdx.map fun (base, index) =>
    let size := (Solcore.Synthesis.Stateful.DynamicBytesExecution.inputBytes base.flags base.payload).size
    let kind := (malformationBank base.payload.length size).getD (choices.getD (2 * index) 0) [.none]
    ⟨base.id, base.flags, base.payload, kind.getD (choices.getD (2 * index + 1) 0 % max kind.length 1) .none⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's flags parity. -/
def completionName (tx : Transaction) : String :=
  match prescribed tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (reverts tx)

/-- Reserve the measured host wrapper before generating its independent step;
the fixed chunk guards lie outside the step budget, and the complete contract
is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.MalformedBytes.programOverhead < nodes do
    throw "node budget is too small for the malformed-bytes wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.MalformedBytes.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated malformed-bytes plan failed full Core admission"
  let _ ← bytesPlan plan
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + guardNodes do
    throw "malformed-bytes contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "malformed-bytes-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices LongBytes.sequenceChoices seed transactions)),
    ("malformationChoices", toJson (Stateful.Sequence.blockChoices malformationChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map completionName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; an
accepted transaction completes with its flags parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "malformed-bytes history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "malformed-bytes history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (reverts tx)) do
          throw "an accepted malformed-bytes transaction did not follow its flags parity"
    prior := current

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
        let emitted ← emit scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "malformed-bytes history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "malformed-bytes-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- None weighs nothing; otherwise one plus the malformation's parameters. -/
def weight : Malformation → Nat
  | .none => 0
  | .short bytes => 1 + bytes
  | .selector mask => 1 + mask
  | .truncate kept => 1 + kept
  | .trailing count pattern => 1 + count + pattern
  | .offset value => 1 + value.val
  | .length value => 1 + value.val
  | .padding pattern => 1 + pattern

def malformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + weight transaction.malformation) 0

def payloadLength (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.payload.length) 0

/-- Flags and payload bytes all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.payload.foldl (fun sum byte => sum + byte.toNat) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the malformation
weight, the payload length, then flags and payload bytes. Every axis is a
natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (malformationWeight candidate < malformationWeight source ∨
      (malformationWeight candidate = malformationWeight source ∧
        (payloadLength candidate < payloadLength source ∨
        (payloadLength candidate = payloadLength source ∧ valueWeight candidate < valueWeight source)))))))

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
  let _ ← (bytesPlan plan).toOption
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

/-- Simpler malformations of the same kind, from the smallest parameter up. -/
def simpler (tx : Transaction) : List Malformation :=
  let bank := (malformationBank tx.payload.length (canonicalSize tx)).getD
    (malformationKinds.idxOf (kindOf tx.malformation)) []
  let ordered := bank.mergeSort fun left right => weight left ≤ weight right
  ordered.filter (weight · < weight tx.malformation)

/-- One-transaction removals first, from the last back, then step reductions.
Then, for each transaction: no malformation, simpler malformations of its kind,
the payload cut to each shorter bank length, the payload zeroed, and flags
reduced to their parity or with the revert bit cleared. Candidates still need
execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation := .none})]
    for malformation in simpler transaction do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation})]
    for length in lengthBank do
      if length < transaction.payload.length then
        raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with payload := tx.payload.take length})]
    raw := raw ++ [(step, replaceAt source.transactions index fun tx =>
      {tx with payload := tx.payload.map fun _ => 0})]
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
      ("functionVersion", Solcore.Synthesis.Core.MalformedBytes.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← emit admitted.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from the long-bytes emission of the step"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the long-bytes wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "malformed-bytes-generated" then
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
      throw "saved origin differs from generated malformed-bytes provenance"
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
  else throw "unsupported malformed-bytes case origin"
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
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.MalformedBytes
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.MalformedCalldataExecution
/-! Execute the original checked malformed-calldata contract over a persistent
account world. A transaction is a canonical `(flags, values)` call of
`run(uint256,uint256[])` together with one malformation of its calldata; the
contract receives the malformed bytes. `stdRejection?` is a second model of
the pinned std's dispatcher and decoder, written over the bytes instead of in
Core, which prescribes each transaction's outcome. Observations report slots
zero to four and the contract's whole committed storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedCalldataExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedCalldata (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-calldata-history.v1"

/-- Calldata of every transaction stays within one KiB. -/
def maxCalldata : Nat := 1024

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- How a transaction's calldata departs from the canonical encoding of its
flags and values. Patterns of trailing bytes are zeros (0), `0xff` (1) or the
ramp `1, 2, 3, ...` (2). -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  values : List Word
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  DynamicArrayExecution.inputBytes tx.flags tx.values

/-- The byte at an index, zero past the end; callers read only present bytes. -/
private def byteAt (bytes : ByteArray) (index : Nat) : Nat :=
  (bytes.data[index]?.map UInt8.toNat).getD 0

private def bigEndian (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun total index => total * 256 + byteAt bytes (offset + index)) 0

private def replaceWord (bytes : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  bytes.extract 0 offset ++ encodeWordBytesBE value ++ bytes.extract (offset + 32) bytes.size

private def patternByte (pattern position : Nat) : UInt8 :=
  match pattern with
  | 0 => 0
  | 1 => 0xff
  | _ => (position + 1).toUInt8

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  let canonical := canonicalBytes tx
  match tx.malformation with
  | .none => canonical
  | .short bytes => canonical.extract 0 bytes
  | .selector mask =>
      let changed := (bigEndian canonical 0 4 ^^^ mask) % 2 ^ 32
      ByteArray.mk #[(changed / 2 ^ 24 % 256).toUInt8, (changed / 2 ^ 16 % 256).toUInt8,
        (changed / 2 ^ 8 % 256).toUInt8, (changed % 256).toUInt8] ++ canonical.extract 4 canonical.size
  | .truncate kept => canonical.extract 0 kept
  | .trailing count pattern => canonical ++ ByteArray.mk ((List.range count).map (patternByte pattern)).toArray
  | .offset value => replaceWord canonical 36 value
  | .length value => replaceWord canonical 68 value

/-- A malformation that changes the canonical calldata within its bounds:
selector prefixes, nonzero 32-bit masks, cuts inside the calldata past the
selector, one to 64 trailing bytes, and any replaced Word. -/
def Malformation.valid (malformation : Malformation) (canonicalSize : Nat) : Bool :=
  match malformation with
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .offset _ | .length _ => true

private def wordAt (bytes : ByteArray) (offset : Nat) : Nat := bigEndian bytes offset 32

/-- The pinned std's decision for `run(uint256,uint256[])` over raw calldata:
the rejecting error selector, or none when the method body runs. Natural
arithmetic cannot wrap, as std's checked word arithmetic does not. -/
def stdRejection? (input : ByteArray) : Option Nat :=
  let size := input.size
  if size < 4 then some Solcore.Synthesis.Core.MalformedCalldata.noSelectorError
  else if bigEndian input 0 4 != Solcore.Synthesis.Core.MalformedCalldata.selector then
    some Solcore.Synthesis.Core.MalformedCalldata.noSelectorError
  else if size < 68 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
  else
    let offset := wordAt input 36
    if offset > size - 4 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
    else if size - (4 + offset) < 32 then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
    else
      let length := wordAt input (4 + offset)
      if length > Solcore.Synthesis.Core.MalformedCalldata.maxLength then
        some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
      else if 32 * length > size - (36 + offset) then some Solcore.Synthesis.Core.MalformedCalldata.truncatedError
      else none

/-- The words std decodes when it accepts: flags, length and every element. -/
def stdDecoded? (input : ByteArray) : Option (Nat × List Nat) :=
  if (stdRejection? input).isSome then none
  else
    let offset := wordAt input 36
    let length := wordAt input (4 + offset)
    some (wordAt input 4, (List.range length).map fun index => wordAt input (36 + offset + 32 * index))

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := DynamicArrayExecution.observedSlots
abbrev slotsJson := DynamicArrayExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => DynamicArrayExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the dynamic-array profile,
with each transaction's malformed calldata as the input. -/
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
      match inputData? transaction, registry.resolve? prior bindings.address with
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

end Solcore.Synthesis.Stateful.MalformedCalldataExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.MalformedCalldataCases
/-! Malformed-calldata cases retain the std-modeling original Core contract
around a checked aggregate step and an ordered history of dynamic-array calls,
each with one malformation of its calldata. The compiled contract is the
dynamic-array one, emitted from the same step. Every transaction records its
malformation, the calldata it sends and the outcome std prescribes for those
bytes. Reductions remove transactions, simplify the step, drop or simplify a
malformation, and then reduce elements and flags. Saved outputs are never an
oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MalformedCalldata
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.MalformedCalldata (CheckedPlan)
open Solcore.Synthesis.Stateful.MalformedCalldataExecution (Malformation Transaction Bindings stdRejection?)

def caseSchema : String := "solcore-lean.semantic-malformed-calldata-case.v1"
def planSchema : String := "solcore-lean.malformed-calldata-plan.v1"
def profileVersion : String := "stateful-malformed-calldata-v1/malformation-sequence-seed-v2"
def templateVersion : String := "std-dispatch-array-fold-slots-count-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-malformed-calldata-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs
abbrev emitterVersion := DynamicArray.emitterVersion
abbrev wrapperVersion := DynamicArray.wrapperVersion

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String := ["none", "short", "selector", "truncate", "trailing", "offset", "length"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"

def patternNames : List String := ["zeros", "ones", "ramp"]

def canonicalSize (tx : Transaction) : Nat :=
  (Solcore.Synthesis.Stateful.MalformedCalldataExecution.canonicalBytes tx).size

def validTransaction (tx : Transaction) : Bool :=
  Storage.validId tx.id && tx.values.length ≤ Solcore.Synthesis.Core.MalformedCalldata.maxElements &&
    tx.malformation.valid (canonicalSize tx) &&
    (Solcore.Synthesis.Stateful.MalformedCalldataExecution.inputBytes tx).size ≤
      Solcore.Synthesis.Stateful.MalformedCalldataExecution.maxCalldata

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all validTransaction = true

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
    else throw "canonical malformed-calldata contract exceeds the 512-node case limit"
  else throw s!"malformed-calldata scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, at most three elements and a valid malformation of at most 1 KiB each"

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]

/-- An error selector as its four bytes. -/
def selectorText (selector : Nat) : String :=
  encodeBytesText (ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8])

def prescribed (tx : Transaction) : Option Nat :=
  stdRejection? (Solcore.Synthesis.Stateful.MalformedCalldataExecution.inputBytes tx)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun value => toString value.val)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MalformedCalldataExecution.calldata tx)),
  ("stdRejection", match prescribed tx with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value ≤ 2 ^ 32 do throw ("malformation " ++ key ++ " is out of range")
  return value

def decodeMalformation (json : Json) : Except String Malformation := do
  let kind ← json.getObjValAs? String "kind"
  if kind = "none" then return .none
  else if kind = "short" then return .short (← natural json "bytes")
  else if kind = "selector" then
    let text ← json.getObjValAs? String "mask"
    unless text.length ≤ 10 do throw "selector mask exceeds 32 bits"
    let some mask := text.toNat? | throw "invalid selector mask"
    return .selector mask
  else if kind = "truncate" then return .truncate (← natural json "kept")
  else if kind = "trailing" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := patternNames.idxOf? name | throw "unknown trailing pattern"
    return .trailing (← natural json "count") pattern
  else if kind = "offset" then return .offset (← word (← json.getObjValAs? String "value"))
  else if kind = "length" then return .length (← word (← json.getObjValAs? String "value"))
  else throw "unknown malformation kind"

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List String) "values"
    unless texts.length ≤ Solcore.Synthesis.Core.MalformedCalldata.maxElements do throw "array exceeds three elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM word,
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransaction transaction do throw "invalid transaction ID, elements or malformation"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "malformed-calldata scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

/-- The dynamic-array plan of the same step, whose source is the compiled contract. -/
def arrayPlan (plan : CheckedPlan) : Except String Solcore.Synthesis.Core.DynamicArray.CheckedPlan := do
  let some arrayPlan := Solcore.Synthesis.Core.DynamicArray.CheckedPlan.ofStep? plan.step |
    throw "the step fails the dynamic-array contract's admission"
  return arrayPlan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported malformed-calldata plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "malformed-calldata contract failed full host-Core admission"
  unless json == planJson plan do throw "malformed-calldata plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ 512 do throw "malformed-calldata contract exceeds the 512-node case limit"
  let _ ← arrayPlan plan
  return plan

def emit (plan : CheckedPlan) : Except String EmittedProgram := do
  (DynamicArray.emit (← arrayPlan plan)).mapError reprStr

abbrev contractJson := DynamicArray.contractJson
abbrev initialStateJson := DynamicArray.initialStateJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("malformedCalldataPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MalformedCalldataExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.MalformedCalldata.version),
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
  let emitted ← emit scenario.plan
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do throw "unsupported semantic malformed-calldata case schema"
  let plan ← checkedPlan (← json.getObjVal? "malformedCalldataPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := 512, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical malformed-calldata plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MalformedCalldataExecution.slotsJson do
    throw "observed slots must be zero through four"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MalformedCalldataExecution.observe scenario.plan scenario.transactions bindings fuel

/-- The malformations a transaction with `length` elements and canonical size
`size` draws from, by kind: none; short calldata; wrong selectors; cuts inside
the head and the tail; trailing bytes; out-of-range, wrapping and overlapping
head offsets; and too long, wrapping, maximal, shorter and zero lengths. -/
def malformationBank (length size : Nat) : List (List Malformation) := [
  [.none],
  [.short 0, .short 1, .short 2, .short 3],
  [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)],
  [.truncate 4, .truncate 36, .truncate 67, .truncate 99, .truncate (size - 32), .truncate (size - 1)],
  [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2],
  [.offset (Word.ofNatModulo (size - 3)), .offset (Word.ofNatModulo (size - 35)), .offset (Word.ofNatModulo (2 ^ 255)),
    .offset (Word.ofNatModulo (2 ^ 256 - 4)), .offset (Word.ofNatModulo (2 ^ 256 - 2)),
    .offset (Word.ofNatModulo (2 ^ 256 - 1)), .offset Word.zero, .offset (Word.ofNatModulo 32)],
  [.length (Word.ofNatModulo (length + 1)), .length (Word.ofNatModulo (2 ^ 251)),
    .length (Word.ofNatModulo (2 ^ 251 + 1)), .length (Word.ofNatModulo (2 ^ 256 - 1)),
    .length (Word.ofNatModulo (length - 1)), .length Word.zero]]

/-- A kind and a parameter for each of three transactions, each the high half of
one draw from a separate stream. The stream starts at SplitMix64's finalizer of
the seed xor its domain, so that consecutive seeds' choices do not step by a
fixed residue. -/
def malformationChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d616c666f726d2d))
  let mut values : Array Nat := #[]
  for bound in [7, 8, 7, 8, 7, 8] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := malformationChoices seed
  (DynamicArray.blockTransactions seed first).zipIdx.map fun (base, index) =>
    let size := (Solcore.Synthesis.Stateful.DynamicArrayExecution.inputBytes base.flags base.values).size
    let bank := (malformationBank base.values.length size).getD (choices.getD (2 * index) 0) [.none]
    ⟨base.id, base.flags, base.values, bank.getD (choices.getD (2 * index + 1) 0 % bank.length) .none⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's flags parity. -/
def completionName (tx : Transaction) : String :=
  match prescribed tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (tx.flags.val % 2 == 1)

/-- Reserve the measured host wrapper before generating its independent step;
the complete contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.MalformedCalldata.programOverhead < nodes do
    throw "node budget is too small for the malformed-calldata wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.MalformedCalldata.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated malformed-calldata plan failed full Core admission"
  let _ ← arrayPlan plan
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes do throw "malformed-calldata contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "malformed-calldata-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices DynamicArray.sequenceChoices seed transactions)),
    ("malformationChoices", toJson (Stateful.Sequence.blockChoices malformationChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map completionName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; an
accepted transaction completes with its flags parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "malformed-calldata history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "malformed-calldata history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (tx.flags.val % 2 == 1)) do
          throw "an accepted malformed-calldata transaction did not follow its flags parity"
    prior := current

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
        let emitted ← emit scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "malformed-calldata history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "malformed-calldata-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- None weighs nothing; otherwise one plus the malformation's parameter. -/
def weight : Malformation → Nat
  | .none => 0
  | .short bytes => 1 + bytes
  | .selector mask => 1 + mask
  | .truncate kept => 1 + kept
  | .trailing count pattern => 1 + count + pattern
  | .offset value => 1 + value.val
  | .length value => 1 + value.val

def malformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + weight transaction.malformation) 0

def elementCount (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + transaction.values.length) 0

def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum value => sum + value.val) (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the malformation
weight, the number of array elements, then flags and element values. Every axis
is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (malformationWeight candidate < malformationWeight source ∨
      (malformationWeight candidate = malformationWeight source ∧
        (elementCount candidate < elementCount source ∨
        (elementCount candidate = elementCount source ∧ valueWeight candidate < valueWeight source)))))))

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
  let _ ← (arrayPlan plan).toOption
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

/-- Simpler malformations of the same kind, from the smallest parameter up. -/
def simpler (tx : Transaction) : List Malformation :=
  let size := canonicalSize tx
  let bank := (malformationBank tx.values.length size).getD
    (malformationKinds.idxOf (kindOf tx.malformation)) []
  let ordered := bank.mergeSort fun left right => weight left ≤ weight right
  ordered.filter (weight · < weight tx.malformation)

/-- One-transaction removals first, from the last back, then step reductions.
Then, for each transaction: no malformation, simpler malformations of its kind,
removal and bank replacement of each element, and bank flags. Candidates still
need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(source.plan.step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨source.plan.step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with malformation := .none})]
    for malformation in simpler transaction do
      raw := raw ++ [(source.plan.step, replaceAt source.transactions index fun tx => {tx with malformation})]
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
      ("functionVersion", Solcore.Synthesis.Core.MalformedCalldata.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← emit admitted.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from the dynamic-array emission of the step"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the dynamic-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "malformed-calldata-generated" then
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
      throw "saved origin differs from generated malformed-calldata provenance"
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
  else throw "unsupported malformed-calldata case origin"
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
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.MalformedCalldata
end

section
-- leanmerge: from Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
/-! Execute the original checked malformed-nested-array contract over a
persistent account world. A transaction is a canonical `(flags, values)` call
of `run(uint256,uint256[][])` together with one malformation of its calldata;
the contract receives the malformed bytes. `stdDecode` is a second model of the
pinned std's dispatcher and lazy decoder, written over the bytes instead of in
Core, which prescribes each transaction's outcome and the Words the body reads.
Observations report slots zero to eight and the contract's whole committed
storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
open Lean Solcore.Core Solcore.ContractRuntime
open Solcore.Synthesis.Core.MalformedNestedArray (CheckedPlan)

def historySchema : String := "solcore-lean.malformed-nested-array-history.v1"

/-- One caller and one installed contract, exactly as for the storage profiles. -/
abbrev Bindings := StorageExecution.Bindings

/-- Canonical values have at most four rows of at most three elements, one row
and one element more than the protocol reads. -/
def maxRows : Nat := 4
def maxColumns : Nat := 3

/-- How a transaction's calldata departs from the canonical encoding of its
flags and values: the outer array's malformations, a replaced table Word of
row `row`, or a replaced length Word of row `row`. -/
inductive Malformation where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | offset (value : Word)
  | length (value : Word)
  | rowOffset (row : Nat) (value : Word)
  | rowLength (row : Nat) (value : Word)
  deriving BEq, Repr

structure Transaction where
  id : String
  flags : Word
  values : List (List Word)
  malformation : Malformation
  deriving BEq

def canonicalBytes (tx : Transaction) : ByteArray :=
  NestedArrayExecution.inputBytes tx.flags tx.values

/-- The canonical offset table starts after the selector, the flags, the head
offset 64 and the outer length. -/
def tableStart : Nat := 100

/-- The byte position of row `row`'s length Word in the canonical encoding. -/
def rowStart (values : List (List Word)) (row : Nat) : Nat :=
  tableStart + (NestedArrayExecution.rowOffsets values).getD row 0

def Malformation.change (values : List (List Word)) : Malformation → StdCalldata.Change
  | .none => .none
  | .short bytes => .short bytes
  | .selector mask => .selector mask
  | .truncate kept => .truncate kept
  | .trailing count pattern => .trailing count pattern
  | .offset value => .word 36 value
  | .length value => .word 68 value
  | .rowOffset row value => .word (tableStart + 32 * row) value
  | .rowLength row value => .word (rowStart values row) value

/-- The calldata a transaction sends. -/
def inputBytes (tx : Transaction) : ByteArray :=
  (tx.malformation.change tx.values).apply (canonicalBytes tx)

/-- A malformation within its bounds; a row malformation names a present row. -/
def Malformation.valid (malformation : Malformation) (values : List (List Word)) (canonicalSize : Nat) : Bool :=
  (match malformation with
    | .rowOffset row _ | .rowLength row _ => row < values.length
    | _ => true) &&
  (malformation.change values).valid canonicalSize

/-- The pinned std's decision for `run(uint256,uint256[][])` over raw calldata,
with the Words the body then reads: the flags, the outer length and the
elements of every row it decodes, rows `i < min(n, 3)` in order. Rows past the
third are never decoded. Otherwise the rejecting error selector. -/
def stdDecode (input : ByteArray) : Except Nat (Nat × Nat × List (List Nat)) := do
  let (flags, offset) ← StdCalldata.dynamicHead? input Solcore.Synthesis.Core.MalformedNestedArray.selector
  let rows ← StdCalldata.arrayAt? input (4 + offset)
  let table := 36 + offset
  let read ← (List.range (min rows Solcore.Synthesis.Core.MalformedNestedArray.readRows)).mapM fun index => do
    let (start, length) ← StdCalldata.rowAt? input table index
    return (List.range length).map fun column => StdCalldata.wordAt input (start + 32 + 32 * column)
  return (flags, rows, read)

def stdRejection? (input : ByteArray) : Option Nat :=
  match stdDecode input with
  | .error selector => some selector
  | .ok _ => none

def stdDecoded? (input : ByteArray) : Option (Nat × Nat × List (List Nat)) := (stdDecode input).toOption

def calldata (tx : Transaction) : String := encodeBytesText (inputBytes tx)

def inputData? (tx : Transaction) : Option HostStorageDriver.InputData :=
  let bytes := inputBytes tx
  if bounded : bytes.size < wordModulus then some ⟨bytes, bounded⟩ else none

abbrev observedSlots := NestedArrayExecution.observedSlots
abbrev slotsJson := NestedArrayExecution.slotsJson

private def worldStorage (world : WorldState) (bindings : Bindings) : Json :=
  match world.account? bindings.address with
  | some account => NestedArrayExecution.storageJson account
  | none => Json.null

private def outcomeFields : FrameOutcome Word → List (String × Json)
  | .returned bytes => [("status", toJson "returned"), ("output", toJson (encodeBytesText bytes))]
  | .reverted bytes => [("status", toJson "reverted"), ("output", toJson (encodeBytesText bytes))]
  | .trapped reason => [("status", toJson "trapped"), ("reason", toJson (toString reason.val))]

/-- Independent original-Core observation, as for the nested-array profile,
with each transaction's malformed calldata as the input. -/
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
      match inputData? transaction, registry.resolve? prior bindings.address with
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

end Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
end

section
-- leanmerge: from Solcore.Synthesis.Source.MalformedNestedArrayCases
/-! Malformed-nested-array cases retain the std-modeling original Core contract
around a checked aggregate step and an ordered history of nested-array calls,
each with one malformation of its calldata. Canonical values have at most four
rows of at most three elements. The compiled contract is the nested-array one,
emitted from the same step. Every transaction records its malformation, the
calldata it sends and the outcome std prescribes for those bytes. Reductions
remove transactions, simplify the step, drop or simplify a malformation, and
then reduce rows, elements and flags. Saved outputs are never an oracle. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Source.MalformedNestedArray
open Lean Solcore.Core Solcore.Synthesis.Core
open Solcore.ContractRuntime (encodeBytesText encodeWordBytesBE)
open Solcore.Synthesis.Core.MalformedNestedArray (CheckedPlan guardNodes)
open Solcore.Synthesis.Stateful.MalformedNestedArrayExecution
  (Malformation Transaction Bindings stdRejection? maxRows maxColumns tableStart rowStart)

def caseSchema : String := "solcore-lean.semantic-malformed-nested-array-case.v1"
def planSchema : String := "solcore-lean.malformed-nested-array-plan.v1"
def profileVersion : String := "stateful-malformed-nested-array-v1/malformation-sequence-seed-v2"
def templateVersion : String := "std-dispatch-lazy-nested-fold-slots-counts-revert-odd-flags-v1"
def corpusSchema : String := "solcore-lean.semantic-malformed-nested-array-corpus.v1"

abbrev boundaryInputs := Storage.boundaryInputs
abbrev emitterVersion := NestedArray.emitterVersion
abbrev wrapperVersion := NestedArray.wrapperVersion

/-- Complete contracts may exceed the step budget by the fixed row checks and guards. -/
def maxProgramNodes : Nat := 512 + guardNodes

/-- Every malformation kind, in catalog order. -/
def malformationKinds : List String :=
  ["none", "short", "selector", "truncate", "trailing", "offset", "length", "row-offset", "row-length"]

def kindOf : Malformation → String
  | .none => "none"
  | .short _ => "short"
  | .selector _ => "selector"
  | .truncate _ => "truncate"
  | .trailing _ _ => "trailing"
  | .offset _ => "offset"
  | .length _ => "length"
  | .rowOffset _ _ => "row-offset"
  | .rowLength _ _ => "row-length"

/-- The row a row malformation replaces a Word of. -/
def rowOf : Malformation → Option Nat
  | .rowOffset row _ | .rowLength row _ => some row
  | _ => none

abbrev patternNames := Stateful.StdCalldata.patternNames

def canonicalSize (tx : Transaction) : Nat :=
  (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.canonicalBytes tx).size

def validValue (values : List (List Word)) : Bool :=
  values.length ≤ maxRows && values.all (·.length ≤ maxColumns)

def validTransaction (tx : Transaction) : Bool :=
  Storage.validId tx.id && validValue tx.values &&
    tx.malformation.valid tx.values (canonicalSize tx) &&
    (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.inputBytes tx).size ≤ Stateful.StdCalldata.maxCalldata

def validTransactions (transactions : List Transaction) : Prop :=
  1 ≤ transactions.length ∧ transactions.length ≤ Stateful.Sequence.maxTransactions ∧
    (transactions.map (·.id)).Nodup ∧ transactions.all validTransaction = true

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
    else throw "canonical malformed-nested-array contract exceeds its case limit"
  else throw s!"malformed-nested-array scenario requires 1..{Stateful.Sequence.maxTransactions} transactions with distinct valid IDs, at most four rows of three elements and a valid malformation of at most 1 KiB each"

def malformationJson : Malformation → Json
  | .none => Json.mkObj [("kind", toJson "none")]
  | .short bytes => Json.mkObj [("kind", toJson "short"), ("bytes", toJson bytes)]
  | .selector mask => Json.mkObj [("kind", toJson "selector"), ("mask", toJson (toString mask))]
  | .truncate kept => Json.mkObj [("kind", toJson "truncate"), ("kept", toJson kept)]
  | .trailing count pattern => Json.mkObj [("kind", toJson "trailing"), ("count", toJson count),
      ("pattern", toJson (patternNames.getD pattern "ramp"))]
  | .offset value => Json.mkObj [("kind", toJson "offset"), ("value", toJson (toString value.val))]
  | .length value => Json.mkObj [("kind", toJson "length"), ("value", toJson (toString value.val))]
  | .rowOffset row value => Json.mkObj [("kind", toJson "row-offset"), ("row", toJson row),
      ("value", toJson (toString value.val))]
  | .rowLength row value => Json.mkObj [("kind", toJson "row-length"), ("row", toJson row),
      ("value", toJson (toString value.val))]

abbrev selectorText := Stateful.StdCalldata.selectorText

def prescribed (tx : Transaction) : Option Nat :=
  stdRejection? (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.inputBytes tx)

def transactionJson (tx : Transaction) : Json := Json.mkObj [
  ("id", toJson tx.id), ("flags", toJson (toString tx.flags.val)),
  ("values", toJson (tx.values.map fun row => row.map fun value => toString value.val)),
  ("malformation", malformationJson tx.malformation),
  ("calldata", toJson (Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.calldata tx)),
  ("stdRejection", match prescribed tx with
    | some selector => toJson (selectorText selector)
    | none => Json.null),
  ("value", toJson "0")]

def transactionsJson (transactions : List Transaction) : Json := toJson (transactions.map transactionJson)

private def word (text : String) : Except String Word := do
  unless text.length ≤ 78 do throw "transaction Word exceeds 78 digits"
  Input.inputWord text

private def natural (json : Json) (key : String) : Except String Nat := do
  let value ← json.getObjValAs? Nat key
  unless value ≤ 2 ^ 32 do throw ("malformation " ++ key ++ " is out of range")
  return value

def decodeMalformation (json : Json) : Except String Malformation := do
  let kind ← json.getObjValAs? String "kind"
  if kind = "none" then return .none
  else if kind = "short" then return .short (← natural json "bytes")
  else if kind = "selector" then
    let text ← json.getObjValAs? String "mask"
    unless text.length ≤ 10 do throw "selector mask exceeds 32 bits"
    let some mask := text.toNat? | throw "invalid selector mask"
    return .selector mask
  else if kind = "truncate" then return .truncate (← natural json "kept")
  else if kind = "trailing" then
    let name ← json.getObjValAs? String "pattern"
    let some pattern := patternNames.idxOf? name | throw "unknown trailing pattern"
    return .trailing (← natural json "count") pattern
  else if kind = "offset" then return .offset (← word (← json.getObjValAs? String "value"))
  else if kind = "length" then return .length (← word (← json.getObjValAs? String "value"))
  else if kind = "row-offset" then
    return .rowOffset (← natural json "row") (← word (← json.getObjValAs? String "value"))
  else if kind = "row-length" then
    return .rowLength (← natural json "row") (← word (← json.getObjValAs? String "value"))
  else throw "unknown malformation kind"

def decodeTransactions (json : Json) : Except String (List Transaction) := do
  let rows ← json.getArr?
  unless 1 ≤ rows.size && rows.size ≤ Stateful.Sequence.maxTransactions do
    throw s!"transaction count must be between 1 and {Stateful.Sequence.maxTransactions}"
  let transactions ← rows.toList.mapM fun row => do
    let texts ← row.getObjValAs? (List (List String)) "values"
    unless texts.length ≤ maxRows && texts.all (·.length ≤ maxColumns) do
      throw "value exceeds four rows of three elements"
    let transaction : Transaction := ⟨← row.getObjValAs? String "id",
      ← word (← row.getObjValAs? String "flags"), ← texts.mapM (·.mapM word),
      ← decodeMalformation (← row.getObjVal? "malformation")⟩
    unless validTransaction transaction do throw "invalid transaction ID, values or malformation"
    unless row == transactionJson transaction do
      throw "transaction differs from canonical ID, flags, values, malformation, calldata, std outcome or zero-value metadata"
    return transaction
  unless validTransactions transactions do
    throw "malformed-nested-array scenario requires distinct valid transaction IDs"
  return transactions

def planJson (plan : CheckedPlan) : Json := Json.mkObj [
  ("schema", toJson planSchema), ("stepProgram", Wire.encodeProgram plan.step.program)]

/-- The nested-array plan of the same step, whose source is the compiled contract. -/
def nestedPlan (plan : CheckedPlan) : Except String Solcore.Synthesis.Core.NestedArray.CheckedPlan := do
  let some nestedPlan := Solcore.Synthesis.Core.NestedArray.CheckedPlan.ofStep? plan.step |
    throw "the step fails the nested-array contract's admission"
  return nestedPlan

def checkedPlan (json : Json) : Except String CheckedPlan := do
  unless (← json.getObjValAs? String "schema") = planSchema do throw "unsupported malformed-nested-array plan schema"
  let step ← Aggregate.checkedFunction (← json.getObjVal? "stepProgram")
  let some plan := CheckedPlan.ofStep? step | throw "malformed-nested-array contract failed full host-Core admission"
  unless json == planJson plan do throw "malformed-nested-array plan differs from its canonical checked representation"
  unless Wire.programNodes plan.program ≤ maxProgramNodes do throw "malformed-nested-array contract exceeds its case limit"
  let _ ← nestedPlan plan
  return plan

def emit (plan : CheckedPlan) : Except String EmittedProgram := do
  (NestedArray.emit (← nestedPlan plan)).mapError reprStr

abbrev contractJson := NestedArray.contractJson
abbrev initialStateJson := NestedArray.initialStateJson

def makeCase (scenario : CheckedScenario) (emitted : EmittedProgram) (origin : Json) (fuel : Nat)
    (revision : GeneratorRevision := .v1) (mask : FeatureMask := FeatureMask.all) : Json :=
  Json.mkObj [
    ("schema", toJson caseSchema), ("malformedNestedArrayPlan", planJson scenario.plan),
    ("program", Wire.encodeProgram scenario.program), ("source", toJson emitted.source),
    ("transactions", transactionsJson scenario.transactions),
    ("initialState", initialStateJson),
    ("observedSlots", Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.slotsJson),
    ("provenance", Json.mkObj <| swarmField revision mask ++ [
      ("origin", origin), ("profileVersion", toJson profileVersion),
      ("functionVersion", toJson Solcore.Synthesis.Core.MalformedNestedArray.version),
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
  let emitted ← emit scenario.plan
  return makeCase scenario emitted origin fuel revision mask

/-- Every origin must reconstruct the fixed host contract, including imports and
reductions. An arbitrary well-typed program is not an admissible replacement. -/
def caseProgram (json : Json) : Except String CheckedScenario := do
  unless (← json.getObjValAs? String "schema") = caseSchema do
    throw "unsupported semantic malformed-nested-array case schema"
  let plan ← checkedPlan (← json.getObjVal? "malformedNestedArrayPlan")
  let transactions ← decodeTransactions (← json.getObjVal? "transactions")
  let program ← (Wire.decodeProgramWithBudget
    {maxDepth := 512, maxNodes := maxProgramNodes, maxIntegerBytes := 4096}
    (← json.getObjVal? "program")).mapError (fun
      | .protocol error => error.toJson.compress
      | .exhausted exhaustion => "Core decode budget exceeded: " ++ reprStr exhaustion)
  unless Wire.encodeProgram program == Wire.encodeProgram plan.program do
    throw "saved original Core program differs from the canonical malformed-nested-array plan"
  unless (← json.getObjVal? "initialState") == initialStateJson do throw "initial storage must be empty"
  unless (← json.getObjVal? "observedSlots") == Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.slotsJson do
    throw "observed slots must be zero through eight"
  unless (← json.getObjValAs? Nat "executionFuel") ≤ 10000000 do throw "saved execution fuel exceeds limit"
  checkedScenario plan transactions

def observe (scenario : CheckedScenario) (bindings : Bindings) (fuel : Nat) : Json :=
  Solcore.Synthesis.Stateful.MalformedNestedArrayExecution.observe scenario.plan scenario.transactions bindings fuel

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- The malformations a transaction draws from, by kind, for row `row` of its
canonical values: none; short calldata; wrong selectors; cuts in the head,
the outer length, the offset table, the last row and the last Word; trailing
bytes; out-of-range, wrapping and overlapping head offsets; too long,
wrapping, maximal, shorter and zero outer lengths; out-of-range, wrapping and
overlapping table Words of the row; and too long, wrapping, shorter and zero
lengths of the row. Changes that leave the canonical calldata as it is and cuts
outside it are left out. -/
def malformationBank (values : List (List Word)) (size row : Nat) : List (List Malformation) :=
  let rows := values.length
  let offsets := Solcore.Synthesis.Stateful.NestedArrayExecution.rowOffsets values
  let entry := offsets.getD row 0
  let other := offsets.getD ((row + 1) % max rows 1) 0
  let width := (values.getD row []).length
  let start := rowStart values row
  let fits := (size - (start + 32)) / 32
  let cuts := ([4, 36, 67, 99, tableStart + 16] ++
      (if rows = 0 then [] else [rowStart values (rows - 1) + 16]) ++ [size - 32, size - 1]).eraseDups.filter
    fun kept => 4 ≤ kept && kept < size
  let rowKinds : List (List Malformation) := if row < rows then [
      ([size - tableStart - 31, size - tableStart, size - tableStart + 1, 2 ^ 255, 2 ^ 256 - 32, 2 ^ 256 - 1, 0,
        other, other + 32].eraseDups.filter (· != entry)).map (.rowOffset row ∘ w),
      ([width + 1, fits, fits + 1, 2 ^ 251, 2 ^ 251 + 1, 2 ^ 256 - 1, width - 1, 0].eraseDups.filter
        (· != width)).map (.rowLength row ∘ w)]
    else [[], []]
  [[.none],
    [.short 0, .short 1, .short 2, .short 3],
    [.selector 1, .selector (2 ^ 31), .selector (2 ^ 32 - 1)],
    cuts.map .truncate,
    [.trailing 1 0, .trailing 31 1, .trailing 32 2, .trailing 33 0, .trailing 64 1, .trailing 64 2],
    [size - 3, size - 35, 2 ^ 255, 2 ^ 256 - 4, 2 ^ 256 - 2, 2 ^ 256 - 1, 0, 32].map (.offset ∘ w),
    ([rows + 1, 2 ^ 251, 2 ^ 251 + 1, 2 ^ 256 - 1, rows - 1, 0].eraseDups.filter (· != rows)).map (.length ∘ w)] ++
    rowKinds

def reverts (tx : Transaction) : Bool := tx.flags.val % 2 == 1

/-- Three outer lengths, four row lengths per transaction, three elements per
row, then the completion pattern. Each choice uses the high half of one draw
from a separate stream: the low bits of a power-of-two LCG have short periods.
The stream starts at SplitMix64's finalizer of the seed xor its domain, so that
consecutive seeds' choices do not step by a fixed residue. -/
def sequenceBounds : List Nat := [5, 5, 5] ++ List.replicate 12 4 ++ List.replicate 36 6 ++ [4]

def sequenceChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6d616c2d6e657374))
  let mut values : Array Nat := #[]
  for bound in sequenceBounds do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- A kind, a parameter and a row for each of three transactions, each the high
half of one draw from a separate stream. The stream starts at SplitMix64's
finalizer of the seed xor its domain, so that consecutive seeds' choices do not
step by a fixed residue. -/
def malformationChoices (seed : Seed) : List Nat := Id.run do
  let mut state := Seed.ofUInt64 (GeneratorV2.mix (seed.toUInt64 ^^^ 0x6e6573742d6d616c))
  let mut values : Array Nat := #[]
  for bound in [9, 9, 4, 9, 9, 4, 9, 9, 4] do
    let (value, next) := state.draw
    values := values.push (value.toNat / 2 ^ 32 % bound)
    state := next
  return values.toList

/-- Transaction `i` has `choices[i]` rows; row `r` has `choices[3 + 4i + r]`
elements, element `c` drawn by `choices[15 + 12i + 3r + c]`; the completion
pattern is `choices[51]`. Its malformation is drawn from the bank by the
kind, parameter and row choices. -/
def blockTransactions (seed : Seed) (first : Nat) : List Transaction :=
  let choices := sequenceChoices seed
  let draws := malformationChoices seed
  let bank := fun index => boundaryInputs.getD (choices.getD index 0) Word.zero
  let parities := NestedArray.parityPatterns.getD (choices.getD 51 0) [false, false, false]
  parities.zipIdx.map fun (odd, index) =>
    let values := (List.range (choices.getD index 0)).map fun row =>
      (List.range (choices.getD (3 + 4 * index + row) 0)).map fun column =>
        bank (15 + 12 * index + 3 * row + column)
    let flags := NestedArray.parityFlags odd
    let size := (Solcore.Synthesis.Stateful.NestedArrayExecution.inputBytes flags values).size
    let row := draws.getD (3 * index + 2) 0 % max values.length 1
    let kind := (malformationBank values size row).getD (draws.getD (3 * index) 0) [.none]
    ⟨"tx-" ++ toString (first + index), flags, values,
      kind.getD (draws.getD (3 * index + 1) 0 % max kind.length 1) .none⟩

/-- The first `count` transactions of the seed's consecutive blocks. -/
def generatedTransactions (seed : Seed) (count : Nat := 3) : List Transaction :=
  Stateful.Sequence.blocks blockTransactions seed count

private def statusName (odd : Bool) : String := if odd then "reverted" else "returned"

/-- The prescribed completion: the std rejection, or the body's flags parity. -/
def completionName (tx : Transaction) : String :=
  match prescribed tx with
  | some selector => "rejected:" ++ selectorText selector
  | none => statusName (reverts tx)

/-- Reserve the measured host wrapper before generating its independent step;
the fixed row checks and guards lie outside the step budget, and the complete
contract is remeasured as the final budget authority. -/
def generatedScenario (seed : Seed) (nodes : Nat) (revision : GeneratorRevision := .v1)
    (transactions : Nat := 3) : Except String (CheckedScenario × Json) := do
  Stateful.Sequence.checkCount transactions
  unless nodes ≤ 512 && Solcore.Synthesis.Core.MalformedNestedArray.programOverhead < nodes do
    throw "node budget is too small for the malformed-nested-array wrapper or exceeds 512"
  let (step, stepOrigin) ← Aggregate.generatedFunction seed
    (nodes - Solcore.Synthesis.Core.MalformedNestedArray.programOverhead) revision
  let some plan := CheckedPlan.ofStep? step | throw "generated malformed-nested-array plan failed full Core admission"
  let _ ← nestedPlan plan
  let scenario ← checkedScenario plan (generatedTransactions seed transactions)
  unless Wire.programNodes scenario.program ≤ nodes + guardNodes do
    throw "malformed-nested-array contract exceeds its requested node budget"
  return (scenario, Stateful.Sequence.recordCount (Json.mkObj [
    ("kind", toJson "malformed-nested-array-generated"), ("seed", toJson (toString seed.toNat)),
    ("finalSeed", ← stepOrigin.getObjVal? "finalSeed"), ("maxProgramNodes", toJson nodes),
    ("stepOrigin", stepOrigin),
    ("sequenceChoices", toJson (Stateful.Sequence.blockChoices sequenceChoices seed transactions)),
    ("malformationChoices", toJson (Stateful.Sequence.blockChoices malformationChoices seed transactions)),
    ("sequenceCompletions", toJson (scenario.transactions.map completionName))]) transactions)

private def rowStatus (row : Json) : Option String := (row.getObjValAs? String "status").toOption

/-- Original Core must give every prescribed outcome: a std rejection reverts
with its selector Word and keeps the prior slots and whole storage; an
accepted transaction completes with its flags parity. -/
def validateGenerated (scenario : CheckedScenario) (fuel : Nat) : Except String Unit := do
  Aggregate.inputSensitive scenario.plan.step fuel
  let observed := observe scenario Solcore.Synthesis.Stateful.StorageExecution.fixtureBindings fuel
  unless (← observed.getObjValAs? String "status") = "complete" do
    throw "malformed-nested-array history exhausted Core fuel"
  let rows ← observed.getObjValAs? (List Json) "transactions"
  unless rows.length == scenario.transactions.length do throw "malformed-nested-array history length changed"
  let mut prior := (← observed.getObjVal? "initialStorage", ← observed.getObjVal? "initialAccountStorage")
  for (row, tx) in rows.zip scenario.transactions do
    let current := (← row.getObjVal? "committedStorage", ← row.getObjVal? "accountStorage")
    match prescribed tx with
    | some selector =>
        unless rowStatus row == some "reverted" &&
            (row.getObjValAs? String "output").toOption ==
              some (encodeBytesText (encodeWordBytesBE (Word.ofNatModulo selector))) do
          throw "original Core does not revert with the prescribed std selector"
        unless current == prior do throw "a std rejection changed the committed storage"
    | none =>
        unless rowStatus row == some (statusName (reverts tx)) do
          throw "an accepted malformed-nested-array transaction did not follow its flags parity"
    prior := current

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
        let emitted ← emit scenario.plan
        validateGenerated scenario fuel
        return (scenario, origin.setObjVal! "validationFuel" (toJson fuel), emitted)
      match result with
      | .error error =>
          let resource := error == "boundary observation exhausted Core fuel" ||
            error == "malformed-nested-array history exhausted Core fuel"
          excluded := excluded.push (Json.mkObj [
            ("seed", toJson (toString seed.toNat)), ("stage", toJson "malformed-nested-array-profile"),
            ("reason", toJson error),
            ("code", toJson (if resource then "validation-out-of-fuel" else "profile-excluded")),
            ("category", toJson (if resource then "inconclusive-resource" else "excluded"))])
      | .ok (scenario, origin, emitted) =>
          cases := cases.push (makeCase scenario emitted origin fuel revision (revision.caseMask seed))
  return Json.mkObj [("schema", toJson corpusSchema),
    ("requested", toJson count), ("attempted", toJson attempted),
    ("status", toJson (if cases.size = count then "complete" else "generation-exhausted")),
    ("excluded", .arr excluded), ("cases", .arr cases)]

/-- None weighs nothing; otherwise one plus the malformation's parameters. -/
def weight : Malformation → Nat
  | .none => 0
  | .short bytes => 1 + bytes
  | .selector mask => 1 + mask
  | .truncate kept => 1 + kept
  | .trailing count pattern => 1 + count + pattern
  | .offset value => 1 + value.val
  | .length value => 1 + value.val
  | .rowOffset row value => 1 + row + value.val
  | .rowLength row value => 1 + row + value.val

def malformationWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction => total + weight transaction.malformation) 0

/-- Every row and every element counts once. -/
def shapeSize (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => sum + 1 + row.length) total) 0

/-- Flags and elements all contribute. -/
def valueWeight (scenario : CheckedScenario) : Nat :=
  scenario.transactions.foldl (fun total transaction =>
    transaction.values.foldl (fun sum row => row.foldl (fun inner value => inner + value.val) sum)
      (total + transaction.flags.val)) 0

/-- Transaction count, complete program size/literals, the malformation
weight, the number of rows and elements, then flags and element values. Every
axis is a natural number. -/
def StrictlySmaller (candidate source : CheckedScenario) : Prop :=
  candidate.transactions.length < source.transactions.length ∨
  (candidate.transactions.length = source.transactions.length ∧
    ((complexity candidate.program.body).StrictlySmaller (complexity source.program.body) ∨
    (complexity candidate.program.body = complexity source.program.body ∧
      (malformationWeight candidate < malformationWeight source ∨
      (malformationWeight candidate = malformationWeight source ∧
        (shapeSize candidate < shapeSize source ∨
        (shapeSize candidate = shapeSize source ∧ valueWeight candidate < valueWeight source)))))))

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
  let _ ← (nestedPlan plan).toOption
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

/-- Simpler malformations of the same kind and row, from the smallest parameter up. -/
def simpler (tx : Transaction) : List Malformation :=
  let bank := (malformationBank tx.values (canonicalSize tx) ((rowOf tx.malformation).getD 0)).getD
    (malformationKinds.idxOf (kindOf tx.malformation)) []
  let ordered := bank.mergeSort fun left right => weight left ≤ weight right
  ordered.filter (weight · < weight tx.malformation)

/-- One-transaction removals first, from the last back, then step reductions.
Then, for each transaction: no malformation, simpler malformations of its kind,
removal of each row, removal of each nonempty row's last element, zeroing every
element, and flags reduced to their parity or with the revert bit cleared.
Candidates still need execution to establish that they preserve a finding. -/
def reductions (source : CheckedScenario) : List (Reduction source) := Id.run do
  let step := source.plan.step
  let mut raw : List (Aggregates.CheckedDAG × List Transaction) := []
  for index in (List.range source.transactions.length).reverse do
    raw := raw ++ [(step,
      (source.transactions.zipIdx.filter (fun (_, current) => current != index)).map Prod.fst)]
  for reduced in Aggregate.reductions ⟨step, Word.zero⟩ do
    raw := raw ++ [(reduced.candidate.function, source.transactions)]
  for (transaction, index) in source.transactions.zipIdx do
    raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation := .none})]
    for malformation in simpler transaction do
      raw := raw ++ [(step, replaceAt source.transactions index fun tx => {tx with malformation})]
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
      ("functionVersion", Solcore.Synthesis.Core.MalformedNestedArray.version), ("templateVersion", templateVersion),
      ("stepProfileVersion", Aggregate.profileVersion), ("stepFunctionVersion", Aggregates.version),
      ("stepTemplateVersion", Aggregate.templateVersion),
      ("emitterVersion", emitterVersion), ("wrapperVersion", wrapperVersion)] do
    unless (← provenance.getObjValAs? String name) = expected do throw (name ++ " changed")
  let origin ← provenance.getObjVal? "origin"
  let emitted ← emit admitted.plan
  unless (← json.getObjValAs? String "source") = emitted.source do
    throw "saved source differs from the nested-array emission of the step"
  unless (← json.getObjVal? "contract") == contractJson emitted do
    throw "saved contract metadata differs from the nested-array wrapper"
  unless (← provenance.getObjVal? "features") == toJson admitted.plan.step.features do throw "saved features differ from checked step"
  let kind ← origin.getObjValAs? String "kind"
  if kind = "malformed-nested-array-generated" then
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
      throw "saved origin differs from generated malformed-nested-array provenance"
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
  else throw "unsupported malformed-nested-array case origin"
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
  return Json.mkObj [("schema", toJson corpusSchema), ("cases", toJson cases)]

end Solcore.Synthesis.Source.MalformedNestedArray
end
