import Solcore.Synthesis.Core.CallReturn
import Solcore.ContractRuntime.CallChainExecution

/-! Checked contracts for a parent that calls a child two or three times in one
method and measures the latest return data around each call. The child
`get(uint256 x)` reads `o = slot 0` and `c = slot 1 + 1`, applies a closed
aggregate step `r = step(x + o)` and writes `r` to slot 0 and `c` to slot 1.
With the class byte `b = x mod 256` and `L = min(b >> 1, 96)`, its data are the
first `L` bytes of `d0 ‖ d1 ‖ d2`, where `d0 = r·K`, `d1 = (c·K) xor x` and
`d2 = d0 xor d1`: reverted when `b` is odd, otherwise returned, both raw.

The parent is in continuation-passing form for the call chain. Its call phase
writes `p + input` to slot 0 and `z = 0` to slot 1, and requests call 1 with
`mix·256 + b_1`, where `mix = input >> 32` and `b_k` is the input's byte
`k - 1`. It keeps seven Words: the target, the input, `mix`, the running sum,
the size the next call's preceding `returndatasize` reads, call 1's copy's
first Word and whether call 1's data have a whole Word. Each later phase reads
the kept Words, the status Word and the call's data at base 256, writes the
call's flag and size, first Word, preceding size, size and window, and either
requests the next call with the size as the next preceding one, or, as the
last phase, writes call 1's first Word re-read once per later call and reverts
with the sum under the input's bit 24, or returns it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallSequence

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallBuilder

def childVersion : String := "core-call-sequence-child-v1"
def parentVersion : String := "core-call-sequence-parent-v1"

/-- `get(uint256)`, the child's one method. -/
def getSelector : Nat := CallReturn.getSelector

/-- The bytes returns' odd multiplier. -/
def multiplier : Nat := CallReturn.multiplier

/-- The child's longest data: three Words. -/
def capacity : Nat := 96

/-- The widest window: one Word. -/
def maxWidth : Nat := 32

/-- The Words each requesting phase keeps: the target, the input, `mix`, the
running sum, the next preceding size, call 1's first Word and whether call 1's
data have a whole Word. -/
def keptWords : Nat := 7

/-- The return data start after the kept Words and the status Word. -/
def base : Nat := 32 * (keptWords + 1)

/-- The parent's slots for `calls` calls: the accumulator, `z`, five per call
and the re-read. -/
def parentSlotCount (calls : Nat) : Nat := 5 * calls + 3

/-- The child's slots: the step result and the call count. -/
def childSlotCount : Nat := 2

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- A window of `width` bytes at `offset` in a call's data. -/
structure Window where
  offset : Nat
  width : Nat
  deriving Repr, BEq, DecidableEq

def Window.valid (window : Window) : Bool := window.offset ≤ capacity && window.width ≤ maxWidth

/-- Two or three calls, each with a valid window. -/
def validWindows (windows : List Window) : Bool :=
  (windows.length == 2 || windows.length == 3) && windows.all Window.valid

/-! ### The child -/

/-- The raw data side: a unit marker, the length Word and three data Words. -/
def rawType : Ty := .product .unit (.product .word (TupleReturn.wordTuple 2))

def childResultType : Ty := .sum rawType (.sum rawType .word)

theorem childResultType_toCore :
    childResultType.toCore = (CoreContractEntryProfile.rawOutcomeV1 2).resultType := by
  simp [childResultType, rawType, Ty.toCore, TupleReturn.wordTuple_toCore,
    CoreContractEntryProfile.resultType, CoreContractEntryProfile.rawBytesType]

private def band (left right : B) : B := bbinary .wordAnd left right
private def bmul (left right : B) : B := bbinary .wordMul left right
private def bxor (left right : B) : B := bbinary .wordXor left right
private def bshr (value : B) (shift : Nat) : B := bbinary .wordShr value (bword shift)

/-- The child with `step` at level 0, then `x`, `o`, `c`, `r`, the two writes,
the length and the three data Words. -/
private def childBody (stepBody : Expr) : B :=
  blet (fun _ => stepBody) fun step =>
  blet (readAt (bword 4)) fun x =>
  blet (sload 0) fun o =>
  blet (badd (sload 1) (bword 1)) fun c =>
  blet (bapply (bvar step) (badd (bvar x) (bvar o))) fun r =>
  blet (sstore 0 (bvar r)) fun _ =>
  blet (sstore 1 (bvar c)) fun _ =>
  blet (bshr (band (bvar x) (bword 255)) 1) fun half =>
  blet (bcond (bgt (bvar half) (bword capacity)) (bword capacity) (bvar half)) fun length =>
  blet (bmul (bvar r) (bword multiplier)) fun d0 =>
  blet (bxor (bmul (bvar c) (bword multiplier)) (bvar x)) fun d1 =>
  blet (bxor (bvar d0) (bvar d1)) fun d2 =>
  let data := bpair bunit (bpair (bvar length) (btuple [bvar d0, bvar d1, bvar d2]))
  bcond (bbitSet (bvar x) 1)
    (binRight rawType (binLeft .word data))
    (binLeft (.sum rawType .word) data)

def childProgramOf (stepBody : Expr) : Program := {
  resultType := childResultType
  dataDefinitions := []
  body := childBody stepBody 0
}

/-- The child's shell, the step apart: measured with a one-node placeholder
step, which is never admitted or run. -/
def childShellNodes : Nat :=
  let placeholder : Program := { resultType := .function .word .word, dataDefinitions := [], body := .word Word.zero }
  programNodes (childProgramOf (.word Word.zero)) - programNodes placeholder

/-! ### The parent -/

/-- A requesting phase's result: the target, the selector, the argument and the
kept Words. -/
def requestType : Ty := .sum (TupleReturn.wordTuple (keptWords + 2)) (.sum .word .word)

/-- The argument of call `k`, from zero: `mix·256` plus the input's byte `k`. -/
private def argument (mix input : Nat) (call : Nat) : B :=
  badd (bmul (bvar mix) (bword 256)) (band (bshr (bvar input) (8 * call)) (bword 255))

/-- The request for call `call` and the kept Words. -/
private def request (target input mix sum previous copy whole : B) (call : Nat) (mixLevel inputLevel : Nat) : B :=
  binLeft (.sum .word .word) (btuple [target, bword getSelector, argument mixLevel inputLevel call,
    target, input, mix, sum, previous, copy, whole])

/-- Read the target at 4 and the input at 36, write `p + input` to slot 0 and
`z = 0` to slot 1, then request call 1. -/
private def callBody : B :=
  blet (readAt (bword 4)) fun target =>
  blet (readAt (bword 36)) fun input =>
  blet (badd (sload 0) (bvar input)) fun accumulator =>
  blet (sstore 0 (bvar accumulator)) fun _ =>
  blet (sstore 1 (bword 0)) fun _ =>
  blet (bshr (bvar input) 32) fun mix =>
  request (bvar target) (bvar input) (bvar mix) (bvar accumulator) (bword 0) (bword 0) (bword 0) 0 mix input

def callProgram : Program := {
  resultType := requestType
  dataDefinitions := []
  body := callBody 0
}

/-- The data's bytes `offset` to `offset + width - 1`, left-aligned in a zero
Word, when they lie inside the `m` bytes at `base`, and otherwise zero: the
Word at `base + offset` when it exists, otherwise the Word ending at the data's
last byte shifted to the offset, then masked to the width. -/
private def window (window : Window) (m : Nat) : B :=
  bcond (bgt (bword (window.offset + window.width)) (bvar m)) (bword 0)
    (band
      (bcond (bgt (bword (window.offset + 32)) (bvar m))
        (bbinary .wordShl (readAt (bsub (badd (bword base) (bvar m)) (bword 32)))
          (bmul (bword 8) (bsub (bword (window.offset + 32)) (bvar m))))
        (readAt (bword (base + window.offset))))
      (bword (CallReturn.keepMask window.width)))

/-- The phase after call `call`, which requests the next call. Call 1's phase
keeps its first Word and whether its data have a whole Word. -/
private def middleBody (call : Nat) (spot : Window) : B :=
  blet inputSize fun size =>
  blet (readAt (bword 0)) fun target =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 64)) fun mix =>
  blet (readAt (bword 96)) fun sum =>
  blet (readAt (bword 128)) fun previous =>
  blet (readAt (bword 160)) fun copy =>
  blet (readAt (bword 192)) fun whole =>
  blet (readAt (bword 224)) fun status =>
  blet (bsub (bvar size) (bword base)) fun m =>
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar m)) (bword 0) (readAt (bword base))) fun first =>
  blet (window spot m) fun copied =>
  blet (sstore (5 * call - 3) (badd (bvar ok) (bmul (bword 2) (bvar m)))) fun _ =>
  blet (sstore (5 * call - 2) (bvar first)) fun _ =>
  blet (sstore (5 * call - 1) (bvar previous)) fun _ =>
  blet (sstore (5 * call) (bvar m)) fun _ =>
  blet (sstore (5 * call + 1) (bvar copied)) fun _ =>
  blet (badd (badd (badd (badd (badd (badd (bvar sum) (bvar ok)) (bmul (bword 2) (bvar m))) (bvar first))
    (bvar previous)) (bvar m)) (bvar copied)) fun total =>
  blet (badd (badd (badd (bvar mix) (bvar first)) (bvar m)) (bvar copied)) fun mixed =>
  let copy' := if call = 1 then bvar first else bvar copy
  let whole' := if call = 1 then bcond (bgt (bword 32) (bvar m)) (bword 0) (bword 1) else bvar whole
  request (bvar target) (bvar input) (bvar mixed) (bvar total) (bvar m) copy' whole' call mixed input

def middleProgram (call : Nat) (spot : Window) : Program := {
  resultType := requestType
  dataDefinitions := []
  body := middleBody call spot 0
}

/-- The phase after the last call, call `calls`: the re-read, the sum and bit
24's revert. -/
private def lastBody (calls : Nat) (spot : Window) : B :=
  blet inputSize fun size =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 96)) fun sum =>
  blet (readAt (bword 128)) fun previous =>
  blet (readAt (bword 160)) fun copy =>
  blet (readAt (bword 192)) fun whole =>
  blet (readAt (bword 224)) fun status =>
  blet (bsub (bvar size) (bword base)) fun m =>
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar m)) (bword 0) (readAt (bword base))) fun first =>
  blet (window spot m) fun copied =>
  blet (bcond (beq (bvar whole) (bword 1)) (bmul (bword (calls - 1)) (bvar copy)) (bword 0)) fun again =>
  blet (sstore (5 * calls - 3) (badd (bvar ok) (bmul (bword 2) (bvar m)))) fun _ =>
  blet (sstore (5 * calls - 2) (bvar first)) fun _ =>
  blet (sstore (5 * calls - 1) (bvar previous)) fun _ =>
  blet (sstore (5 * calls) (bvar m)) fun _ =>
  blet (sstore (5 * calls + 1) (bvar copied)) fun _ =>
  blet (sstore (5 * calls + 2) (bvar again)) fun _ =>
  blet (badd (badd (badd (badd (badd (badd (badd (bvar sum) (bvar ok)) (bmul (bword 2) (bvar m))) (bvar first))
    (bvar previous)) (bvar m)) (bvar copied)) (bvar again)) fun total =>
  bcond (bbitSet (bvar input) (2 ^ 24))
    (binRight .word (binLeft .word (bvar total)))
    (binLeft (.sum .word .word) (bvar total))

def lastResultType : Ty := .sum .word (.sum .word .word)

def lastProgram (calls : Nat) (spot : Window) : Program := {
  resultType := lastResultType
  dataDefinitions := []
  body := lastBody calls spot 0
}

/-- The phases after calls 1 to `n - 1`, which request the next call. -/
def middlePrograms (windows : List Window) : List Program :=
  windows.dropLast.zipIdx.map fun (spot, index) => middleProgram (index + 1) spot

def lastProgramOf (windows : List Window) : Program :=
  lastProgram windows.length (windows.getLastD ⟨0, 0⟩)

def callNodes : Nat := programNodes callProgram

/-- Every contract is bounded by 1,024 nodes. -/
def maxContractNodes : Nat := 1024

/-! ### The checked plan -/

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  windows : List Window
  valid : validWindows windows = true
  childChecked : (childProgramOf step.program.body).check = true
  callChecked : callProgram.check = true
  middlesChecked : (middlePrograms windows).all Program.check = true
  lastChecked : (lastProgramOf windows).check = true

namespace CheckedPlan

def childProgram (plan : CheckedPlan) : Program := childProgramOf plan.step.program.body
def callProgram (_plan : CheckedPlan) : Program := CallSequence.callProgram
def middlePrograms (plan : CheckedPlan) : List Program := CallSequence.middlePrograms plan.windows
def lastProgram (plan : CheckedPlan) : Program := lastProgramOf plan.windows
def calls (plan : CheckedPlan) : Nat := plan.windows.length

def ofParts? (step : Aggregates.CheckedDAG) (windows : List Window) : Option CheckedPlan :=
  if valid : validWindows windows = true then
    if childChecked : (childProgramOf step.program.body).check = true then
      if callChecked : CallSequence.callProgram.check = true then
        if middlesChecked : (CallSequence.middlePrograms windows).all Program.check = true then
          if lastChecked : (lastProgramOf windows).check = true then
            some ⟨step, windows, valid, childChecked, callChecked, middlesChecked, lastChecked⟩
          else none
        else none
      else none
    else none
  else none

theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

theorem callWellTyped (plan : CheckedPlan) : plan.callProgram.WellTyped :=
  Program.check_full_sound plan.callChecked

theorem lastWellTyped (plan : CheckedPlan) : plan.lastProgram.WellTyped :=
  Program.check_full_sound plan.lastChecked

def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def callCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.callProgram.toCore, Program.check_promotes_current plan.callChecked⟩

def lastCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.lastProgram.toCore, Program.check_promotes_current plan.lastChecked⟩

def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 plan.childCode 2 childResultType_toCore

theorem requestType_toCore :
    requestType.toCore = (CoreContractEntryProfile.wordTupleOutcomeV1 (keptWords + 1)).resultType := by
  simp [requestType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType]

/-- A requesting phase, of the call phase's result type. -/
def requestContract (program : Program) (checked : program.check = true)
    (typed : program.resultType = requestType) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨program.toCore, Program.check_promotes_current checked⟩ (keptWords + 1)
    (by
      change program.resultType.toCore = _
      rw [typed, requestType_toCore])

def callContract (plan : CheckedPlan) : CheckedCoreContract :=
  requestContract plan.callProgram plan.callChecked rfl

/-- Each middle program of `windows` is a requesting phase. -/
theorem middlePrograms_resultType (windows : List Window) :
    ∀ program ∈ CallSequence.middlePrograms windows, program.resultType = requestType := by
  intro program member
  simp only [CallSequence.middlePrograms, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

def middleContracts (plan : CheckedPlan) : List CheckedCoreContract :=
  plan.middlePrograms.attach.map fun ⟨program, member⟩ =>
    requestContract program (List.all_eq_true.mp plan.middlesChecked program member)
      (middlePrograms_resultType plan.windows program member)

def lastContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.wordOutcomeV1 plan.lastCode rfl

theorem middleContracts_entryProfile (plan : CheckedPlan) :
    ∀ phase ∈ plan.middleContracts, phase.entryProfile = .wordTupleOutcomeV1 (keptWords + 1) := by
  intro phase member
  simp only [middleContracts, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  rfl

/-- The parent in continuation-passing form for the call chain. -/
def parent (plan : CheckedPlan) : CallChainParent := {
  call := plan.callContract
  middles := plan.middleContracts
  last := plan.lastContract
  keptWords := keptWords
  call_entryProfile := rfl
  middles_entryProfile := plan.middleContracts_entryProfile
  last_entryProfile := rfl
}

theorem childContract_entryProfile (plan : CheckedPlan) :
    plan.childContract.entryProfile = .rawOutcomeV1 2 := rfl

theorem middleContracts_length (plan : CheckedPlan) :
    plan.middleContracts.length = plan.calls - 1 := by
  simp [middleContracts, CheckedPlan.middlePrograms, CallSequence.middlePrograms, calls]

end CheckedPlan
end Solcore.Synthesis.Core.CallSequence
