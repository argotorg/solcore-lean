import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! Two checked host contracts for one value-forwarding Word call. The parent
adds its input and call value to slot zero, calls the child with an explicit
amount, records the child's typed outcome and selects a root return or revert.
The child folds its own call value into a closed aggregate step and records the
value it accepted. Account transfers, child rollback and root rollback belong
to the balanced top-level runtime and its nested scheduler. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.ForwardedCall

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-forwarded-value-call-v1"
def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)
private def bitSet (input : Expr) (bit : Nat) : Expr :=
  .binary .wordEq (.binary .wordAnd input (word bit)) (word bit)
private def returned (payload : Expr) : Expr := .inLeft (.sum .word .word) payload
private def reverted (payload : Expr) : Expr := .inRight .word (.inLeft .word payload)
private def trapped (reason : Expr) : Expr := .inRight .word (.inRight .word reason)

/-- Collapse the four call outcomes to an adjusted payload or a trap reason.
Each case introduces its own payload binder; no parent local is used here. -/
private def consumeChild (call : Expr) : Expr :=
  .caseE call (.inLeft .word (.var 0))
    (.caseE (.var 0) (.inLeft .word (.binary .wordAdd (.var 0) (word 1)))
      (.caseE (.var 0) (.inRight .word (.var 0)) (.inRight .word (.var 0))))

/-- Successful child-outcome decoding adds a payload binder above seven parent
locals; the original input is then local eight, after the result binding. -/
private def finishParent : Expr :=
  .letE (host 1 8 (.pair (word 1) (.var 0)))
    (.letE (.binary .wordAdd (host 0 9 (word 0)) (host 0 9 (word 1)))
      (.ifE (bitSet (.var 8) 2) (reverted (.var 0)) (returned (.var 0))))

/-- The target, input and amount Words follow the selector; the call value is
read through the host. The child receives the input Word and value `amount`. -/
private def parentExpression : Expr :=
  .letE (readInput 0 4)
    (.letE (readInput 1 36)
      (.letE (readInput 2 68)
        (.letE (host 4 3 .unit)
          (.letE (.binary .wordAdd (.binary .wordAdd (host 0 4 (word 0)) (.var 2)) (.var 0))
            (.letE (host 1 5 (.pair (word 0) (.var 0)))
              (.letE (consumeChild (host 11 6 (.pair (.var 5) (.pair (.var 3) (.var 4)))))
                (.caseE (.var 0) finishParent (trapped (.var 0)))))))))

private def childExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 0)
      (.letE (host 4 2 .unit)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 1))
            (.letE (.apply (.var 4) (.binary .wordAdd (.binary .wordAdd (.var 3) (.var 2)) (.var 1)))
              (.letE (host 1 6 (.pair (word 0) (.var 0)))
                (.letE (host 1 7 (.pair (word 1) (.binary .wordAdd (.var 2) (.var 4))))
                  (.ifE (bitSet (.var 6) 1) (reverted (.var 2)) (returned (.var 2))))))))))

def canonicalParentProgram : Program := {
  resultType := resultType, dataDefinitions := [], body := parentExpression }

def canonicalChildProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType, dataDefinitions := [], body := childExpression step.program.body }

def combinedNodes (step : Aggregates.CheckedDAG) : Nat :=
  programNodes canonicalParentProgram + programNodes (canonicalChildProgram step)

/-- Both wrappers, with the child step counted once. The dummy expression only
measures syntax and is never checked or executed as a contract. -/
def programOverhead : Nat :=
  programNodes canonicalParentProgram +
    programNodes {resultType := resultType, dataDefinitions := [], body := childExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  parentChecked : canonicalParentProgram.check = true
  childChecked : (canonicalChildProgram step).check = true

namespace CheckedPlan

def parentProgram (_plan : CheckedPlan) : Program := canonicalParentProgram
def childProgram (plan : CheckedPlan) : Program := canonicalChildProgram plan.step

def ofStep? (step : Aggregates.CheckedDAG) : Option CheckedPlan :=
  if parentChecked : canonicalParentProgram.check = true then
    if childChecked : (canonicalChildProgram step).check = true then
      some ⟨step, parentChecked, childChecked⟩
    else none
  else none

theorem parentWellTyped (plan : CheckedPlan) : plan.parentProgram.WellTyped :=
  Program.check_full_sound plan.parentChecked
theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

def parentCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.parentProgram.toCore, Program.check_promotes_current plan.parentChecked⟩
def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def parentContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.parentCode rfl
def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.childCode rfl

theorem parentContract_program (plan : CheckedPlan) :
    plan.parentContract.code.program = plan.parentProgram.toCore := rfl
theorem childContract_program (plan : CheckedPlan) :
    plan.childContract.code.program = plan.childProgram.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.ForwardedCall
