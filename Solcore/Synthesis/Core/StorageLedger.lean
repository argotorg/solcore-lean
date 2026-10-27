import Solcore.Synthesis.Core.StorageMapping

/-! A checked sender-keyed ledger over the Keccak-addressed mapping of
`StorageMapping`. The calldata of `run(uint256 flags, uint256 recipient,
uint256 amount, uint256 input)` holds four Words; the sender is the
invocation's caller, read with the `callerAddress` host request. The contract
credits `B = entries[sender] + step(input)` at `keccak256(1 ++ sender)`,
reverts with `B` when the amount exceeds it, and otherwise writes `B - amount`
to the sender's entry, adds the amount to the entry at `keccak256(1 ++
recipient)`, increments the counter at slot zero and rereads all three. The
original flags parity then selects return or revert. The public contract
runtime commits or rolls back the resulting working world.

Slots are hashed with the mapping profile's closure, built from the Core
Keccak-f[1600] permutation and digest builders the Hull import path uses for
its `keccak256` builtin and proved against the independent `KeccakSemantics`
specification. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StorageLedger

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-sender-ledger-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

/-- The counter field's slot and the mapping field's base slot, as for the mapping. -/
def counterSlot : Nat := StorageMapping.counterSlot
def mappingSlot : Nat := StorageMapping.mappingSlot

/-- The fixed Keccak closure's size, which lies outside the step's node budget. -/
def hashNodes : Nat := StorageMapping.hashNodes

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- After the result binding, the flags are local eleven; both entry slots, the
credited balance, the sender, the calldata Words, the step and the hash
closure remain in scope. -/
private def completion : Expr :=
  .ifE (.binary .wordEq (.binary .wordAnd (.var 11) (word 1)) (word 1))
    (.inRight .word (.inLeft .word (.var 0)))
    (.inLeft (.sum .word .word) (.var 0))

/-- With the credited balance as local zero: write the sender's and the
recipient's entries, increment the counter, reread all three and complete. -/
private def transfer : Expr :=
  .letE (host 1 10 (.pair (.var 2) (.binary .wordSub (.var 0) (.var 5))))
    (.letE (host 1 11 (.pair (.var 2) (.binary .wordAdd (host 0 11 (.var 2)) (.var 6))))
      (.letE (host 1 12 (.pair (word counterSlot) (.binary .wordAdd (host 0 12 (word counterSlot)) (word 1))))
        (.letE (.binary .wordAdd
            (.binary .wordAdd (host 0 13 (.var 5)) (host 0 13 (.var 4)))
            (host 0 13 (word counterSlot)))
          completion)))

private def contractExpression (stepBody : Expr) : Expr :=
  .letE StorageMapping.hashClosure
    (.letE stepBody
      (.letE (readAt 2 (word 4))
        (.letE (readAt 3 (word 36))
          (.letE (readAt 4 (word 68))
            (.letE (readAt 5 (word 100))
              (.letE (host 5 6 .unit)
                (.letE (.apply (.var 6) (.pair (word mappingSlot) (.var 0)))
                  (.letE (.apply (.var 7) (.pair (word mappingSlot) (.var 4)))
                    (.letE (.binary .wordAdd (host 0 9 (.var 1)) (.apply (.var 7) (.var 3)))
                      (.ifE (.binary .wordGt (.var 5) (.var 0))
                        (.inRight .word (.inLeft .word (.var 0)))
                        transfer))))))))))

def canonicalProgram (step : Aggregates.CheckedDAG) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression step.program.body
}

def canonicalNodes (step : Aggregates.CheckedDAG) : Nat := programNodes (canonicalProgram step)

/-- Syntax-only overhead of the protocol around the step, without the fixed
Keccak closure; the placeholder is never admitted or run. -/
def programOverhead : Nat :=
  programNodes {resultType := resultType, dataDefinitions := [], body := contractExpression (word 0)} -
    programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0} - hashNodes

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

def contract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.code rfl

theorem contract_program (plan : CheckedPlan) : plan.contract.code.program = plan.program.toCore := rfl

end CheckedPlan
end Solcore.Synthesis.Core.StorageLedger
