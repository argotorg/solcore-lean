import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked call-value protocol around a closed aggregate step. The ABI
supplies a flags Word and an input Word; the `callValue` host function supplies
the transaction's value. The contract writes `step(input + value + slot0)` to
slot zero and adds the value to slot one, so slot one is the value the contract
has accepted. The original flags parity then selects return or revert. The
public balanced runtime transfers the value before the root runs and commits or
refunds it together with the working world; the Core expression itself never
reads a balance. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallValue

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-call-value-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- The binder at `position`, counted from the outermost, in a frame with
`depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- After the two Unit write binders, the flags are binder one and the result
binder six. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (bound 9 1) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (bound 9 6)))
    (.inLeft (.sum .word .word) (bound 9 6))

/-- Every host application names its exact local depth. The binders are the
step, flags, input, value, both slot reads, the result and the two writes;
slot zero is written before slot one. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 4 3 .unit)
          (.letE (host 0 4 (word 0))
            (.letE (host 0 5 (word 1))
              (.letE (.apply (bound 6 0) (.binary .wordAdd (.binary .wordAdd (bound 6 2) (bound 6 3)) (bound 6 4)))
                (.letE (host 1 7 (.pair (word 0) (bound 7 6)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (bound 8 5) (bound 8 3))))
                    completion))))))))

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

/-- The checked step and the value the contract holds after deployment. The
deployment value is part of the deployed world, not of the Core program. -/
structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  deploymentValue : Word
  checked : (canonicalProgram step).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step

def ofParts? (step : Aggregates.CheckedDAG) (deploymentValue : Word) : Option CheckedPlan :=
  if checked : (canonicalProgram step).check = true then some ⟨step, deploymentValue, checked⟩ else none

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
end Solcore.Synthesis.Core.CallValue
