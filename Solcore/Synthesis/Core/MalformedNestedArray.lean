import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Synthesis.Core.NestedArray
import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.CheckedCoreContract

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

/-- The std rejections this contract produces. `ArrayOutOfBounds()` cannot
arise, since the protocol guards every row index by the outer length and every
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
