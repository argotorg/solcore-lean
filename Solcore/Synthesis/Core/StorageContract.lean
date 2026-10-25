import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A fixed two-slot storage protocol around a checked, closed aggregate DAG.
Only storageRead, storageWrite and inputDataWordBE? from the Wire host table are
used by this wrapper. Differential cases supply exactly the run(uint256)
selector and one ABI Word; malformed calldata behavior is outside this profile.
The original Core entry closure is bound once for each contract invocation. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageContract

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-contract-v1"

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- Fixed host indices are offset by the complete current local prefix,
including both Unit sequencing binders after the storage writes. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (word 4)) (word 0) (.var 0))
      (.letE (.apply (.var 2) (word 0))
        (.letE (.apply (.var 3) (word 1))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (word 0) (.var 0)))
              (.letE (.apply (.var 7) (.pair (word 1) (.binary .wordAdd (.var 2) (word 1))))
                (.binary .wordAdd (.apply (.var 7) (word 0)) (.apply (.var 7) (word 1)))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := .word
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Measured wrapper overhead, using a one-node expression only to count syntax.
The placeholder is never admitted as contract code or executed. -/
def programOverhead : Nat :=
  programNodes {resultType := .word, dataDefinitions := [], body := contractExpression (word 0)} -
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

def wordCode (plan : CheckedPlan) : CheckedHostCoreWordProgram := ⟨plan.code, rfl⟩

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.returnWord plan.wordCode

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.StorageContract
