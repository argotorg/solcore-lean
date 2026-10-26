import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

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
