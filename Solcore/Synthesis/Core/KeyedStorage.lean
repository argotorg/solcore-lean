import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked keyed-storage protocol around a closed aggregate step. The ABI
supplies a full-width slot key and an input Word. The contract writes the key
slot, its wrapping successor and the fixed counter slot zero in that order, so
keys zero and maximum alias the counter. All three slots are reread before the
original input parity selects return or revert. The public contract runtime
commits or rolls back the resulting working world; the Core expression itself
does not restore storage. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.KeyedStorage

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-keyed-storage-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The fixed counter slot. Keys zero and maximum alias it directly and through
the wrapping successor write respectively. -/
def counterSlot : Nat := 0

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- After the result binding, the original input is local ten; the three Unit
write binders and three final reads remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 10) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- Every host application names its exact local depth. Writes occur in the
order key, key + 1, counter; the later write wins when slots alias. -/
private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (.var 1))
          (.letE (host 0 4 (word counterSlot))
            (.letE (.apply (.var 4) (.binary .wordAdd (.var 2) (.var 1)))
              (.letE (host 1 6 (.pair (.var 4) (.var 0)))
                (.letE (host 1 7 (.pair (.binary .wordAdd (.var 5) (word 1)) (.var 3)))
                  (.letE (host 1 8 (.pair (word counterSlot) (.binary .wordAdd (.var 3) (word 1))))
                    (.letE (host 0 9 (.var 7))
                      (.letE (host 0 10 (.binary .wordAdd (.var 8) (word 1)))
                        (.letE (host 0 11 (word counterSlot))
                          (.letE (.binary .wordAdd (.binary .wordAdd (.var 2) (.var 1)) (.var 0))
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
end Solcore.Synthesis.Core.KeyedStorage
