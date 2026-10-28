import Solcore.Synthesis.Core.StorageMapping
import Solcore.Synthesis.Core.EventLog

/-! A checked protocol of a bounded loop over Keccak-addressed mapping entries
with one log per iteration. The ABI supplies `run(uint256 flags, uint256
input)`; the contract runs `input & mask` iterations of a closed aggregate
step. Iteration `i` uses the key `(input & ~7) | (i & keyMask)` and its entry
slot `keccak256(1 ++ key)`, the pinned std's layout for a mapping at base slot
one. It reads the entry and slot zero, writes `step(entry + slot 0 + input)` to
the entry and then to slot zero, and emits one log whose data is the written
value and whose topics are `i` and the key. Afterwards the result is slot zero
plus the iteration count, and the original flags parity selects return or
revert.

The hash closure is the mapping profile's, bound once. Logs use the event-log
profile's framing of Core's one word-log primitive: a header naming two topics
and one data Word, the data record, then the two topic records. The loop is
`mask` finite ordinal guards with literal ordinals and no counter cell; the
emitted source's while loop is a separate implementation. The public contract
runtime commits or rolls back the working world and journal together. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.KeccakLoop

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime

def version : String := "core-keccak-loop-contract-v1"
def resultType : Ty := .sum .word (.sum .word .word)

def AllowedMask (mask : Nat) : Prop := mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7

instance (mask : Nat) : Decidable (AllowedMask mask) := inferInstanceAs
  (Decidable (mask = 0 ∨ mask = 1 ∨ mask = 3 ∨ mask = 7))

/-- The largest admitted loop mask, and so the most iterations a transaction runs. -/
def maxIterations : Nat := 7

/-- The accumulator field's slot and the mapping's base slot. -/
def accumulatorSlot : Nat := 0
def mappingSlot : Nat := Solcore.Synthesis.Core.StorageMapping.mappingSlot

/-- Each log has two topics, the ordinal and the key, and one data Word. -/
def logSite : Solcore.Synthesis.Core.EventLog.Site := {guard := 0, topics := 2, dataWords := 1}

/-- The bits of the input that keep their place in every key. -/
def highMask : Nat := 2 ^ 256 - 8

private def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def host (index depth : Nat) (argument : Expr) : Expr := .apply (.var (index + depth)) argument
/-- The binder at `position`, counted from the outermost, in a frame of `depth` binders. -/
private def bound (depth position : Nat) : Expr := .var (depth - 1 - position)
/-- An absent calldata Word reads as zero; canonical cases never reach it. -/
private def readInput (depth offset : Nat) : Expr := .caseE (host 8 depth (word offset)) (word 0) (.var 0)

/-- `let` each value in turn, then the body. -/
private def chain : List Expr → Expr → Expr
  | [], body => body
  | value :: rest, body => .letE value (chain rest body)

/-- Outer binders: the hash closure, the step, the flags, the input and the limit. -/
private def hashPosition : Nat := 0
private def stepPosition : Nat := 1
private def flagsPosition : Nat := 2
private def inputPosition : Nat := 3
private def limitPosition : Nat := 4
private def outerDepth : Nat := 5

/-- Iteration `ordinal` after the earlier iterations' Unit binders. Its own
binders are the key, the slot, the old entry, slot zero, the value, both writes
and the log frame's first three records; the frame's last record ends it. -/
private def iteration (keyMask ordinal : Nat) : Expr :=
  let d := outerDepth + ordinal
  let key := d
  let slot := d + 1
  let old := d + 2
  let accumulator := d + 3
  let value := d + 4
  .ifE (.binary .wordGt (bound d limitPosition) (word ordinal))
    (chain [
      .binary .wordOr (.binary .wordAnd (bound d inputPosition) (word highMask)) (word (ordinal &&& keyMask)),
      .apply (bound (d + 1) hashPosition) (.pair (word mappingSlot) (bound (d + 1) key)),
      host 0 (d + 2) (bound (d + 2) slot),
      host 0 (d + 3) (word accumulatorSlot),
      .apply (bound (d + 4) stepPosition)
        (.binary .wordAdd (.binary .wordAdd (bound (d + 4) old) (bound (d + 4) accumulator)) (bound (d + 4) inputPosition)),
      host 1 (d + 5) (.pair (bound (d + 5) slot) (bound (d + 5) value)),
      host 1 (d + 6) (.pair (word accumulatorSlot) (bound (d + 6) value)),
      host 13 (d + 7) (.pair (word (Solcore.Synthesis.Core.EventLog.headerTag logSite)) (word 0)),
      host 13 (d + 8) (.pair (word (Solcore.Synthesis.Core.EventLog.dataTag 1)) (bound (d + 8) value)),
      host 13 (d + 9) (.pair (word (Solcore.Synthesis.Core.EventLog.topicTag 1)) (word ordinal))]
      (host 13 (d + 10) (.pair (word (Solcore.Synthesis.Core.EventLog.topicTag 2)) (bound (d + 10) key))))
    .unit

private def iterations (keyMask : Nat) : Nat → Nat → Expr → Expr
  | 0, _, rest => rest
  | remaining + 1, ordinal, rest => .letE (iteration keyMask ordinal) (iterations keyMask remaining (ordinal + 1) rest)

/-- After the guards: the result is slot zero plus the limit, which odd flags revert. -/
private def completion (mask : Nat) : Expr :=
  let d := outerDepth + mask
  .letE (.binary .wordAdd (host 0 d (word accumulatorSlot)) (bound d limitPosition))
    (.ifE (.binary .wordEq (.binary .wordAnd (bound (d + 1) flagsPosition) (word 1)) (word 1))
      (.inRight .word (.inLeft .word (.var 0)))
      (.inLeft (.sum .word .word) (.var 0)))

private def contractExpression (hash stepBody : Expr) (mask keyMask : Nat) : Expr :=
  .letE hash
    (.letE stepBody
      (.letE (readInput 2 4)
        (.letE (readInput 3 36)
          (.letE (.binary .wordAnd (bound 4 inputPosition) (word mask))
            (iterations keyMask mask 0 (completion mask))))))

def canonicalProgram (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Program := {
  resultType := resultType
  dataDefinitions := []
  body := contractExpression Solcore.Synthesis.Core.StorageMapping.hashClosure step.program.body mask keyMask
}

def canonicalNodes (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Nat :=
  programNodes (canonicalProgram step mask keyMask)

/-- The fixed Keccak closure, which lies outside a case's node budget. -/
abbrev hashNodes : Nat := Solcore.Synthesis.Core.StorageMapping.hashNodes

private def placeholderNodes (mask : Nat) : Nat :=
  let body := contractExpression Solcore.Synthesis.Core.StorageMapping.hashClosure (word 0) mask 0
  programNodes {resultType := resultType, dataDefinitions := [], body := body}

/-- Syntax-only measurement of the shell, the wrapper without the hash closure
and the guards, using a one-node placeholder step that is never admitted or
run, as the mapping profile measures its overhead. The shell lies inside a
case's node budget. -/
def shellNodes : Nat :=
  placeholderNodes 0 - programNodes {resultType := .function .word .word, dataDefinitions := [], body := word 0} - hashNodes

/-- The guards of `mask` iterations, which lie outside a case's node budget. -/
def guardNodes (mask : Nat) : Nat := placeholderNodes mask - placeholderNodes 0

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  mask : Nat
  keyMask : Nat
  allowed : AllowedMask mask
  allowedKey : AllowedMask keyMask
  checked : (canonicalProgram step mask keyMask).check = true

namespace CheckedPlan

def program (plan : CheckedPlan) : Program := canonicalProgram plan.step plan.mask plan.keyMask

def ofParts? (step : Aggregates.CheckedDAG) (mask keyMask : Nat) : Option CheckedPlan :=
  if allowed : AllowedMask mask then
    if allowedKey : AllowedMask keyMask then
      if checked : (canonicalProgram step mask keyMask).check = true then
        some ⟨step, mask, keyMask, allowed, allowedKey, checked⟩
      else none
    else none
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
end Solcore.Synthesis.Core.KeccakLoop
