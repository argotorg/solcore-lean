import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked protocol that returns a `bytes` value of at most 64 bytes. The ABI
supplies `run(uint256 flags, uint256 input, uint256 length)`; the contract reads
`prior`, slot 0, and `last`, slot 2, applies a closed aggregate step to
`prior + input`, writes the result `r` to slot 0, slot 1 plus one to slot 1 and
the input to slot 2, then rereads slot 1 as `count`. Odd flags revert with `r`;
even flags return the first `length mod 65` bytes of the data Words `r · K` and
`(count · K) xor last` under the bounded `bytes` entry convention. The public
contract runtime commits or rolls back the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.BytesReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-bytes-return-contract-v1"

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The longest returned value; the contract reads its length Word modulo one
more. -/
def maxLength : Nat := CoreContractEntryProfile.boundedBytesLimit

def lengthModulus : Nat := maxLength + 1

/-- The odd constant whose products spread a data Word over its leading bytes. -/
def multiplier : Nat := 0x9e3779b97f4a7c15f39cc0605cedc8341082276bf3a27251f86c6a11d0c18e95

/-- A non-empty value's length tag and two data Words. -/
def dataType : Ty := .product .word (.product .word .word)

/-- The returned side of the bounded convention: empty, or tagged data. -/
def bytesType : Ty := .sum .unit dataType

def resultType : Ty := .sum bytesType (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- In a frame of eleven binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the length Word, the input, the flags and the step at 4 to 10.
Odd flags revert with `r`. Otherwise the length is the length Word modulo 65:
zero returns the empty value, and any other length its tag `length - 1` with
the data Words `r · K` and `(count · K) xor last`. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 9) (word 1)) (word 1))
    (.inRight bytesType (.inLeft .word (.var 4)))
    (.letE (.binary .wordMod (.var 7) (word lengthModulus))
      (.ifE (.binary .wordEq (.var 0) (word 0))
        (.inLeft (.sum .word .word) (.inLeft dataType .unit))
        (.inLeft (.sum .word .word) (.inRight .unit
          (.pair (.binary .wordSub (.var 0) (word 1))
            (.pair (.binary .wordMul (.var 5) (word multiplier))
              (.binary .wordXor (.binary .wordMul (.var 1) (word multiplier)) (.var 6))))))))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (readInput 3 68)
          (.letE (host 0 4 (word 0))
            (.letE (host 0 5 (word 2))
              (.letE (.apply (.var 5) (.binary .wordAdd (.var 1) (.var 3)))
                (.letE (host 1 7 (.pair (word 0) (.var 0)))
                  (.letE (host 1 8 (.pair (word 1) (.binary .wordAdd (host 0 8 (word 1)) (word 1))))
                    (.letE (host 1 9 (.pair (word 2) (.var 6)))
                      (.letE (host 0 10 (word 1))
                        completion))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat :=
  programNodes (canonicalProgram step)

/-- Syntax-only measurement of the shell, the wrapper without the step, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

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

theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType = CoreContractEntryProfile.boundedBytesOutcomeV1.resultType :=
  rfl

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.boundedBytesOutcomeV1 plan.code plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = .boundedBytesOutcomeV1 := rfl

end CheckedPlan
end Solcore.Synthesis.Core.BytesReturn
