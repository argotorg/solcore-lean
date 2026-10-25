import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked two-slot protocol with a typed rollback outcome. Both writes and
the final reads run before the original ABI input selects return or revert.
The public contract runtime commits or rolls back the resulting working world;
the Core expression itself does not restore storage or simulate a transaction. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageRollback

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-rollback-contract-v1"

def resultType : Ty := .sum .word (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)

/-- After the result binding, the original input is at index six. The two Unit
write binders remain in scope. The captured result is the tentative slot sum. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 6) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (.caseE (.apply (.var 9) (word 4)) (word 0) (.var 0))
      (.letE (.apply (.var 2) (word 0))
        (.letE (.apply (.var 3) (word 1))
          (.letE (.apply (.var 3) (.binary .wordAdd (.var 2) (.var 1)))
            (.letE (.apply (.var 6) (.pair (word 0) (.var 0)))
              (.letE (.apply (.var 7) (.pair (word 1) (.binary .wordAdd (.var 2) (word 1))))
                (.letE (.binary .wordAdd (.apply (.var 7) (word 0)) (.apply (.var 7) (word 1)))
                  completion)))))))

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
end Solcore.Synthesis.Core.StorageRollback
