import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked protocol that returns a static tuple of two to four Words. The ABI
supplies `run(uint256 flags, uint256 input)`; the contract reads `prior`, slot
0, and `last`, slot 2, applies a closed aggregate step to `prior + input`,
writes the result `r` to slot 0, slot 1 plus one to slot 1 and the input to
slot 2, then rereads slot 1 as `count`. Odd flags revert with `r`; even flags
return the first `arity` Words of `(r, count, prior, last)` under the static
Word-tuple entry convention. The public contract runtime commits or rolls back
the resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.TupleReturn

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-tuple-return-contract-v1"

def AllowedArity (arity : Nat) : Prop := arity = 2 ∨ arity = 3 ∨ arity = 4

instance (arity : Nat) : Decidable (AllowedArity arity) := inferInstanceAs
  (Decidable (arity = 2 ∨ arity = 3 ∨ arity = 4))

/-- The largest admitted arity, which returns every protocol Word. -/
def maxArity : Nat := 4

/-- Slot zero, the call count and the last input. -/
def slotCount : Nat := 3

/-- The right-nested Wire product of `count + 1` Words. -/
def wordTuple : Nat → Ty
  | 0 => .word
  | count + 1 => .product .word (wordTuple count)

theorem wordTuple_toCore (count : Nat) :
    (wordTuple count).toCore = CoreContractEntryProfile.wordTupleType count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp [wordTuple, Ty.toCore, CoreContractEntryProfile.wordTupleType, ih]

def resultType (arity : Nat) : Ty := .sum (wordTuple (arity - 1)) (.sum .word .word)

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- Right-nested pairs of the listed Words; one Word stands alone. -/
private def tupleOf : List Expr → Expr
  | [] => .unit
  | [last] => last
  | head :: rest => .pair head (tupleOf rest)

/-- In a frame of ten binders: `count` at 0, three Unit writes, then `r`,
`last`, `prior`, the input, the flags and the step at 4 to 9. Odd flags revert
with `r`; otherwise the first `arity` of `(r, count, prior, last)` return. -/
private def completion (arity : Nat) : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 8) (word 1)) (word 1))
    (.inRight (wordTuple (arity - 1)) (.inLeft .word (.var 4)))
    (.inLeft (.sum .word .word) (tupleOf ([.var 4, .var 0, .var 6, .var 5].take arity)))

private def contractExpression (stepBody : Expr) (arity : Nat) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (host 0 3 (word 0))
          (.letE (host 0 4 (word 2))
            (.letE (.apply (.var 4) (.binary .wordAdd (.var 1) (.var 2)))
              (.letE (host 1 6 (.pair (word 0) (.var 0)))
                (.letE (host 1 7 (.pair (word 1) (.binary .wordAdd (host 0 7 (word 1)) (word 1))))
                  (.letE (host 1 8 (.pair (word 2) (.var 5)))
                    (.letE (host 0 9 (word 1))
                      (completion arity))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (arity : Nat) : Program := {
  resultType := resultType arity
  dataDefinitions := []
  body := contractExpression step.program.body arity
}

def canonicalNodes (step : Aggregates.CheckedDAG) (arity : Nat) : Nat :=
  programNodes (canonicalProgram step arity)

/-- Syntax-only measurement of the shell, the wrapper without the step, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes (arity : Nat) : Nat :=
  programNodes {resultType := resultType arity, dataDefinitions := [], body := contractExpression (word 0) arity} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  arity : Nat
  allowed : AllowedArity arity
  checked : (canonicalProgram step arity).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.arity

def ofParts? (step : Aggregates.CheckedDAG) (arity : Nat) : Option CheckedPlan :=
  if allowed : AllowedArity arity then
    if checked : (canonicalProgram step arity).check = true then some ⟨step, arity, allowed, checked⟩ else none
  else none

theorem check (plan : CheckedPlan) : plan.program.check = true := plan.checked

theorem wellTyped (plan : CheckedPlan) : plan.program.WellTyped :=
  Program.check_full_sound plan.checked

theorem hostChecked (plan : CheckedPlan) : plan.program.toCore.checkHost = true :=
  Program.check_promotes_current plan.checked

def code (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.program.toCore, plan.hostChecked⟩

theorem arity_le (plan : CheckedPlan) : plan.arity ≤ maxArity := by
  rcases plan.allowed with arity | arity | arity <;> simp [arity, maxArity]

/-- The tuple convention's `extraWords + 2` Words are the plan's arity. -/
theorem arity_eq (plan : CheckedPlan) : plan.arity - 2 + 2 = plan.arity := by
  rcases plan.allowed with arity | arity | arity <;> simp [arity]

theorem resultType_eq (plan : CheckedPlan) :
    plan.code.program.resultType =
      (CoreContractEntryProfile.wordTupleOutcomeV1 (plan.arity - 2)).resultType := by
  have predecessor : plan.arity - 1 = plan.arity - 2 + 1 := by
    rcases plan.allowed with arity | arity | arity <;> simp [arity]
  change (resultType plan.arity).toCore = _
  simp [resultType, Ty.toCore, wordTuple_toCore, CoreContractEntryProfile.resultType, predecessor]

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 plan.code (plan.arity - 2) plan.resultType_eq

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

theorem contract_entryProfile (plan : CheckedPlan) :
    plan.contract.entryProfile = .wordTupleOutcomeV1 (plan.arity - 2) := rfl

end CheckedPlan
end Solcore.Synthesis.Core.TupleReturn
