import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

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

/-- The std rejections this contract produces. `ArrayOutOfBounds()` cannot
arise, since the protocol guards every index by the length, and the non-payable
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
