import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

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
