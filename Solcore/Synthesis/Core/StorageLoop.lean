import Solcore.Synthesis.Core.AggregateDAG
import Solcore.Core.Wire.Codec.Program
import Solcore.ContractRuntime.CheckedCoreContract

/-! A checked protocol of a bounded loop over declared slots. The ABI supplies
`run(uint256 flags, uint256 input)`; the contract runs `input & mask`
iterations of a closed aggregate step. Iteration `i` reads slots 0, 1, `1 + i`
and `2 + i`, applies the step to their wrapping sum plus the input, and writes
the result to slot `2 + i` and then to slot zero. Afterwards slot one grows by
the iteration count, and the original flags parity selects return or revert of
slot zero plus slot one. The loop is `mask` finite ordinal guards with literal
slots and no counter cell; the emitted source's while loop and counter are a
separate implementation. The public contract runtime commits or rolls back the
resulting working world. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageLoop

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-storage-loop-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The largest admitted mask, and so the most iterations a transaction runs. -/
def maxIterations : Nat := 7

/-- Slot zero, slot one and one slot for each iteration. -/
def slotCount : Nat := 2 + maxIterations

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (locals offset : Nat) : Expr :=
  .caseE (host 8 locals (word offset)) (word 0) (.var 0)

/-- Iteration `ordinal` in a frame of `4 + ordinal` binders: the earlier
guards' Unit binders, then the limit, input, flags and step at `ordinal` to
`ordinal + 3`. Its four reads bind slots 0, 1, `1 + ordinal` and
`2 + ordinal`; the step's result is written to slot `2 + ordinal`, then to
slot zero. -/
private def iteration (ordinal : Nat) : Expr :=
  let locals := 4 + ordinal
  .ifE (.binary .wordGt (.var ordinal) (word ordinal))
    (.letE (host 0 locals (word 0))
      (.letE (host 0 (locals + 1) (word 1))
        (.letE (host 0 (locals + 2) (word (1 + ordinal)))
          (.letE (host 0 (locals + 3) (word (2 + ordinal)))
            (.letE (.apply (.var (ordinal + 7))
                (.binary .wordAdd (.binary .wordAdd (.binary .wordAdd (.binary .wordAdd
                  (.var 3) (.var 2)) (.var 1)) (.var 0)) (.var (ordinal + 5))))
              (.letE (host 1 (locals + 5) (.pair (word (2 + ordinal)) (.var 0)))
                (host 1 (locals + 6) (.pair (word 0) (.var 1)))))))))
    .unit

private def iterations : Nat → Nat → Expr → Expr
  | 0, _, rest => rest
  | remaining + 1, ordinal, rest => .letE (iteration ordinal) (iterations remaining (ordinal + 1) rest)

/-- After the guards, `4 + mask` binders: the limit is local `mask` and the
flags local `mask + 2`. Slot one grows by the limit; the result is slot zero
plus slot one, which odd flags revert. -/
private def completion (mask : Nat) : Expr :=
  let locals := 4 + mask
  .letE (.binary .wordAdd (host 0 locals (word 1)) (.var mask))
    (.letE (host 1 (locals + 1) (.pair (word 1) (.var 0)))
      (.letE (.binary .wordAdd (host 0 (locals + 2) (word 0)) (host 0 (locals + 2) (word 1)))
        (.ifE (.binary .wordEq (.binary .wordAnd (.var (mask + 5)) (word 1)) (word 1))
          (.inRight .word (.inLeft .word (.var 0)))
          (.inLeft (.sum .word .word) (.var 0)))))

private def contractExpression (stepBody : Expr) (mask : Nat) : Expr :=
  .letE stepBody
    (.letE (readInput 1 4)
      (.letE (readInput 2 36)
        (.letE (.binary .wordAnd (.var 0) (word mask))
          (iterations mask 0 (completion mask)))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask : Nat) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body mask
}

def canonicalNodes (step : Aggregates.CheckedDAG) (mask : Nat) : Nat :=
  programNodes (canonicalProgram step mask)

private def placeholderNodes (mask : Nat) : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0) mask}

/-- Syntax-only measurement of the shell, the wrapper without guards, using a
one-node placeholder step that is never admitted or run. The shell lies inside
a case's node budget. -/
def shellNodes : Nat :=
  placeholderNodes 0 - programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0}

/-- The guards of `mask` iterations, which lie outside a case's node budget. -/
def guardNodes (mask : Nat) : Nat := placeholderNodes mask - placeholderNodes 0

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  allowed : AllowedMask mask
  checked : (canonicalProgram step mask).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask

def ofParts? (step : Aggregates.CheckedDAG) (mask : Nat) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if checked : (canonicalProgram step mask).check = true then some ⟨step, mask, allowed, checked⟩ else none
  else none

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

theorem mask_le (plan : CheckedPlan) : plan.mask ≤ maxIterations := by
  rcases plan.allowed with mask | mask | mask | mask <;> simp [mask, maxIterations]

end CheckedPlan
end Solcore.Synthesis.Core.StorageLoop
