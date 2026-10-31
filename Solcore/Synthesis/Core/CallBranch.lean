import Solcore.Synthesis.Core.CallSequence
import Solcore.ContractRuntime.CallChoiceExecution

/-! Checked contracts for a parent whose calls sit in branches and loops, so
that the input decides how many calls a transaction makes. The child is
`CallSequence`'s child. The parent has one to three sites in program order,
each a branch or a loop, whose bounds number the potential calls, the
positions, from zero. Position `q`'s argument is `mix·256` plus the input's
byte `q`; site `i`'s control bits are the input's bits `24 + 2i` and `25 + 2i`;
bit 30 reverts the parent and `mix = input >> 32`.

The parent is in continuation-passing form for the choice chain: a call phase
and one resume program, all choice phases. Each phase defines every site's
steps as lambdas over a state of `mix`, the calls made, the latest data's size
and a loop's counter: a site's entry reads the size before it and calls or
skips, a loop's iteration calls while its counter is below its limit and the
latest size differs from its stop length, and a site's exit reads the size and
the exit window after it. The last lambda writes the call count, sums the slots
and finishes or reverts. The call phase writes slot 0 and `z = 0`, then enters
site 0 with no data; the resume phase writes the reads after its call, kept as
its position, then continues that call's site. A request keeps five Words: the
target, the input, `mix`, the position and the calls made with it. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallBranch

open Solcore.Core (Word)
open Solcore.Core.Wire
open Solcore.ContractRuntime
open Solcore.Synthesis.Core.CallBuilder
open Solcore.Synthesis.Core.CallSequence (Window childProgramOf childResultType childResultType_toCore)

def parentVersion : String := "core-call-branch-parent-v1"

/-- `get(uint256)`, the child's one method. -/
def getSelector : Nat := CallSequence.getSelector

/-- The child's longest data: three Words. -/
def capacity : Nat := CallSequence.capacity

/-- The most calls a transaction makes. -/
def maxCalls : Nat := 3

/-- The Words each request keeps: the target, the input, `mix`, the position
and the calls made with it. -/
def keptWords : Nat := 5

/-- The return data start after the kept Words and the status Word. -/
def base : Nat := 32 * (keptWords + 1)

/-- The input bit that reverts the parent. -/
def revertBit : Nat := 30

/-- Site `index`'s first control bit. -/
def controlBit (index : Nat) : Nat := 24 + 2 * index

inductive Kind where
  | branch
  | loop
  deriving Repr, BEq, DecidableEq

/-- One call site: a branch of bound one, or a loop of bound one to three that
stops on its stop length, with the window read right after each call and the
one read after the site. -/
structure Site where
  kind : Kind
  bound : Nat
  stop : Nat
  callWindow : Window
  exitWindow : Window
  deriving Repr, BEq, DecidableEq

def Site.valid (site : Site) : Bool :=
  site.callWindow.valid && site.exitWindow.valid &&
    match site.kind with
    | .branch => site.bound == 1 && site.stop == 0
    | .loop => 1 ≤ site.bound && site.bound ≤ maxCalls && site.stop ≤ capacity

/-- The number of positions. -/
def positions (sites : List Site) : Nat := (sites.map (·.bound)).sum

/-- One to three valid sites with at most three positions. -/
def validSites (sites : List Site) : Bool :=
  1 ≤ sites.length && sites.length ≤ 3 && sites.all Site.valid && positions sites ≤ maxCalls

/-- Site `index`'s first position. -/
def firstPosition (sites : List Site) (index : Nat) : Nat := positions (sites.take index)

/-- The site of position `position`. -/
def siteOf (sites : List Site) (position : Nat) : Nat :=
  ((List.range sites.length).filter fun index => firstPosition sites index ≤ position).length - 1

/-- Site `index`'s three slots: the size before it, then the size and the exit
window after it. -/
def siteSlot (index : Nat) : Nat := 2 + 3 * index

/-- Position `position`'s four slots: the flag plus twice the size, the first
Word, the size and the call window after its call. -/
def positionSlot (sites : List Site) (position : Nat) : Nat := 2 + 3 * sites.length + 4 * position

/-- The slot of the number of calls made. -/
def countSlot (sites : List Site) : Nat := positionSlot sites (positions sites)

/-- The parent's slots: the accumulator, `z`, three per site, four per position
and the call count. -/
def parentSlotCount (sites : List Site) : Nat := countSlot sites + 1

def childSlotCount : Nat := CallSequence.childSlotCount

private def w (value : Nat) : Word := Word.ofNatModulo value

private def band (left right : B) : B := bbinary .wordAnd left right
private def bmul (left right : B) : B := bbinary .wordMul left right
private def bshr (value shift : B) : B := bbinary .wordShr value shift

/-! ### The parent -/

/-- A choice phase's result: the choosing Word, the target, the selector, the
argument and the kept Words, or a reverted Word, or a trap. -/
def choiceType : Ty := .sum (TupleReturn.wordTuple (keptWords + 3)) (.sum .word .word)

/-- The state of each site's lambdas: `mix`, the calls made, the latest data's
size and a loop's counter. -/
def stateType : Ty := .product .word (.product .word (.product .word .word))

private def state (mix calls size counter : B) : B := bpair mix (bpair calls (bpair size counter))
private def mixOf (value : B) : B := bfirst value
private def callsOf (value : B) : B := bfirst (bsecond value)
private def sizeOf (value : B) : B := bfirst (bsecond (bsecond value))
private def counterOf (value : B) : B := bsecond (bsecond (bsecond value))

/-- The request for the call at `position`, keeping the target, the input,
`mix`, the position and the calls made with it. -/
private def request (target input mix calls position : B) : B :=
  binLeft (.sum .word .word) (btuple [bword 1, target, bword getSelector,
    badd (bmul mix (bword 256)) (band (bshr input (bmul (bword 8) position)) (bword 255)),
    target, input, mix, position, badd calls (bword 1)])

/-- Finish with `value` as the returned Word. -/
private def finishWith (value : B) : B :=
  binLeft (.sum .word .word) (btuple ([bword 0, value] ++ List.replicate (keptWords + 2) (bword 0)))

/-- The data's bytes `offset` to `offset + width - 1`, left-aligned in a zero
Word, when they lie inside the `size` bytes at `base`, and otherwise zero: the
Word at `base + offset` when it exists, otherwise the Word ending at the data's
last byte shifted to the offset, then masked to the width. -/
private def window (spot : Window) (size : B) : B :=
  bcond (bgt (bword (spot.offset + spot.width)) size) (bword 0)
    (band
      (bcond (bgt (bword (spot.offset + 32)) size)
        (bbinary .wordShl (readAt (bsub (badd (bword base) size) (bword 32)))
          (bmul (bword 8) (bsub (bword (spot.offset + 32)) size)))
        (readAt (bword (base + spot.offset))))
      (bword (CallReturn.keepMask spot.width)))

/-- Zero the four slots of `position`, which no call reached. -/
private def zeroPosition (sites : List Site) (position : Nat) : B :=
  blet (sstore (positionSlot sites position) (bword 0)) fun _ =>
  blet (sstore (positionSlot sites position + 1) (bword 0)) fun _ =>
  blet (sstore (positionSlot sites position + 2) (bword 0)) fun _ =>
  sstore (positionSlot sites position + 3) (bword 0)

/-- The finishing lambda: the call count, the sum of every slot, and bit 30's
revert. -/
private def finishBody (sites : List Site) (input : Nat) : Nat → B := fun value =>
  blet (sstore (countSlot sites) (callsOf (bvar value))) fun _ =>
  blet (((List.range (countSlot sites + 1)).map sload).foldl badd (bword 0)) fun total =>
  bcond (bbitSet (bvar input) (2 ^ revertBit))
    (binRight (TupleReturn.wordTuple (keptWords + 3)) (binLeft .word (bvar total)))
    (finishWith (bvar total))

/-- Site `index`'s exit: the size and the exit window after it, then the next
site's entry, or the finish. -/
private def exitBody (site : Site) (index next : Nat) : Nat → B := fun value =>
  blet (sizeOf (bvar value)) fun size =>
  blet (sstore (siteSlot index + 1) (bvar size)) fun _ =>
  blet (window site.exitWindow (bvar size)) fun copied =>
  blet (sstore (siteSlot index + 2) (bvar copied)) fun _ =>
  bapply (bvar next) (state (badd (badd (mixOf (bvar value)) (bvar size)) (bvar copied))
    (callsOf (bvar value)) (bvar size) (bword 0))

/-- A loop's iteration at its counter: a call while the counter is below the
limit and the latest size differs from the stop length, otherwise zeros for
the positions left, then the exit. -/
private def iterateBody (sites : List Site) (site : Site) (index target input exit : Nat) : Nat → B := fun value =>
  let first := firstPosition sites index
  blet (counterOf (bvar value)) fun counter =>
  blet (band (bshr (bvar input) (bword (controlBit index))) (bword 3)) fun requested =>
  blet (bcond (bgt (bvar requested) (bword site.bound)) (bword site.bound) (bvar requested)) fun limit =>
  blet (bcond (bgt (bvar limit) (bvar counter))
    (bcond (beq (sizeOf (bvar value)) (bword site.stop)) (bword 0) (bword 1)) (bword 0)) fun go =>
  bcond (beq (bvar go) (bword 1))
    (request (bvar target) (bvar input) (mixOf (bvar value)) (callsOf (bvar value)) (badd (bword first) (bvar counter)))
    (((List.range site.bound).foldr (fun offset rest =>
        blet (bcond (bgt (bword (offset + 1)) (bvar counter)) (zeroPosition sites (first + offset)) bunit) fun _ => rest)
      (bapply (bvar exit) (bvar value))))

/-- Site `index`'s entry: the size before it, then a branch's call or zeros,
or a loop's first iteration. -/
private def enterBody (sites : List Site) (site : Site) (index target input exit : Nat) (iterate : Option Nat) :
    Nat → B := fun value =>
  let first := firstPosition sites index
  blet (sstore (siteSlot index) (sizeOf (bvar value))) fun _ =>
  match site.kind, iterate with
  | .loop, some loop =>
      bapply (bvar loop) (state (mixOf (bvar value)) (callsOf (bvar value)) (sizeOf (bvar value)) (bword 0))
  | _, _ =>
      bcond (bbitSet (bvar input) (2 ^ controlBit index))
        (request (bvar target) (bvar input) (mixOf (bvar value)) (callsOf (bvar value)) (bword first))
        (blet (zeroPosition sites first) fun _ => bapply (bvar exit) (bvar value))

/-- The lambdas of one site. -/
structure Levels where
  enter : Nat
  exit : Nat
  iterate : Option Nat

/-- Define the lambdas of sites `index` down to 0, the lambda after site
`index` being `next`, then continue with every site's levels, from site 0. -/
private def defineFrom (sites : List Site) (target input : Nat) :
    Nat → Nat → List Levels → (List Levels → B) → B
  | index, next, defined, rest =>
      let site := sites.getD index ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
      blet (blam stateType choiceType (exitBody site index next)) fun exit =>
      let enter := fun (iterate : Option Nat) =>
        blet (blam stateType choiceType (enterBody sites site index target input exit iterate)) fun entry =>
          let defined' := ⟨entry, exit, iterate⟩ :: defined
          match index with
          | 0 => rest defined'
          | previous + 1 => defineFrom sites target input previous entry defined' rest
      match site.kind with
      | .loop =>
          blet (blam stateType choiceType (iterateBody sites site index target input exit)) fun loop =>
            enter (some loop)
      | .branch => enter none
termination_by index _ _ _ => index

/-- Every site's lambdas after the finish, then `rest` with their levels. -/
private def withSites (sites : List Site) (target input : Nat) (rest : List Levels → B) : B :=
  blet (blam stateType choiceType (finishBody sites input)) fun finish =>
  defineFrom sites target input (sites.length - 1) finish [] rest

/-- Read the target at 4 and the input at 36, write `p + input` to slot 0 and
`z = 0` to slot 1, then enter site 0 with no data. -/
private def callBody (sites : List Site) : B :=
  blet (readAt (bword 4)) fun target =>
  blet (readAt (bword 36)) fun input =>
  blet (sstore 0 (badd (sload 0) (bvar input))) fun _ =>
  blet (sstore 1 (bword 0)) fun _ =>
  blet (bshr (bvar input) (bword 32)) fun mix =>
  withSites sites target input fun levels =>
    bapply (bvar (levels.headD ⟨0, 0, none⟩).enter) (state (bvar mix) (bword 0) (bword 0) (bword 0))

/-- After the call at `position`: its four slots from the status Word and the
data, then the rest of its site. -/
private def afterCall (sites : List Site) (levels : List Levels) (position mix calls status size : Nat) : B :=
  let index := siteOf sites position
  let site := sites.getD index ⟨.branch, 1, 0, ⟨0, 0⟩, ⟨0, 0⟩⟩
  let siteLevels := levels.getD index ⟨0, 0, none⟩
  blet (bcond (beq (bvar status) (bword 1)) (bword 1) (bword 0)) fun ok =>
  blet (bcond (bgt (bword 32) (bvar size)) (bword 0) (readAt (bword base))) fun firstWord =>
  blet (window site.callWindow (bvar size)) fun copied =>
  blet (sstore (positionSlot sites position) (badd (bvar ok) (bmul (bword 2) (bvar size)))) fun _ =>
  blet (sstore (positionSlot sites position + 1) (bvar firstWord)) fun _ =>
  blet (sstore (positionSlot sites position + 2) (bvar size)) fun _ =>
  blet (sstore (positionSlot sites position + 3) (bvar copied)) fun _ =>
  let after := state (badd (badd (badd (bvar mix) (bvar firstWord)) (bvar size)) (bvar copied)) (bvar calls) (bvar size)
    (bword (position - firstPosition sites index + 1))
  match siteLevels.iterate with
  | some loop => bapply (bvar loop) after
  | none => bapply (bvar siteLevels.exit) after

/-- Dispatch on the kept position, from `position` on. -/
private def dispatch (sites : List Site) (levels : List Levels) (kept mix calls status size : Nat) : Nat → B
  | position =>
      if position + 1 ≥ positions sites then afterCall sites levels position mix calls status size
      else bcond (beq (bvar kept) (bword position)) (afterCall sites levels position mix calls status size)
        (dispatch sites levels kept mix calls status size (position + 1))
termination_by position => positions sites - position
decreasing_by omega

/-- Read the kept Words, the status Word and the data's size, then continue
after the kept position's call. -/
private def resumeBody (sites : List Site) : B :=
  blet inputSize fun total =>
  blet (readAt (bword 0)) fun target =>
  blet (readAt (bword 32)) fun input =>
  blet (readAt (bword 64)) fun mix =>
  blet (readAt (bword 96)) fun position =>
  blet (readAt (bword 128)) fun calls =>
  blet (readAt (bword 160)) fun status =>
  blet (bsub (bvar total) (bword base)) fun size =>
  withSites sites target input fun levels =>
    dispatch sites levels position mix calls status size 0

def callProgram (sites : List Site) : Program := {
  resultType := choiceType
  dataDefinitions := []
  body := callBody sites 0
}

def resumeProgram (sites : List Site) : Program := {
  resultType := choiceType
  dataDefinitions := []
  body := resumeBody sites 0
}

/-- The child is bounded by 1,024 nodes. -/
def maxChildNodes : Nat := CallSequence.maxContractNodes

/-- Each parent phase is bounded by 2,048 nodes. -/
def maxPhaseNodes : Nat := 2048

/-! ### The checked plan -/

structure CheckedPlan where private mk ::
  step : Aggregates.CheckedDAG
  sites : List Site
  valid : validSites sites = true
  childChecked : (childProgramOf step.program.body).check = true
  callChecked : (callProgram sites).check = true
  resumeChecked : (resumeProgram sites).check = true

namespace CheckedPlan

def childProgram (plan : CheckedPlan) : Program := childProgramOf plan.step.program.body
def callProgram (plan : CheckedPlan) : Program := CallBranch.callProgram plan.sites
def resumeProgram (plan : CheckedPlan) : Program := CallBranch.resumeProgram plan.sites
def positions (plan : CheckedPlan) : Nat := CallBranch.positions plan.sites

def ofParts? (step : Aggregates.CheckedDAG) (sites : List Site) : Option CheckedPlan :=
  if valid : validSites sites = true then
    if childChecked : (childProgramOf step.program.body).check = true then
      if callChecked : (CallBranch.callProgram sites).check = true then
        if resumeChecked : (CallBranch.resumeProgram sites).check = true then
          some ⟨step, sites, valid, childChecked, callChecked, resumeChecked⟩
        else none
      else none
    else none
  else none

theorem childWellTyped (plan : CheckedPlan) : plan.childProgram.WellTyped :=
  Program.check_full_sound plan.childChecked

theorem callWellTyped (plan : CheckedPlan) : plan.callProgram.WellTyped :=
  Program.check_full_sound plan.callChecked

theorem resumeWellTyped (plan : CheckedPlan) : plan.resumeProgram.WellTyped :=
  Program.check_full_sound plan.resumeChecked

def childCode (plan : CheckedPlan) : CheckedHostCoreProgram :=
  ⟨plan.childProgram.toCore, Program.check_promotes_current plan.childChecked⟩

def childContract (plan : CheckedPlan) : CheckedCoreContract :=
  CheckedCoreContract.rawOutcomeV1 plan.childCode 2 childResultType_toCore

theorem choiceType_toCore :
    choiceType.toCore = (CoreContractEntryProfile.wordTupleOutcomeV1 (keptWords + 2)).resultType := by
  simp [choiceType, Ty.toCore, TupleReturn.wordTuple_toCore, CoreContractEntryProfile.resultType]

/-- A choice phase of `program`, of the choice result type. -/
def choiceContract (program : Program) (checked : program.check = true)
    (typed : program.resultType = choiceType) : CheckedCoreContract :=
  CheckedCoreContract.wordTupleOutcomeV1 ⟨program.toCore, Program.check_promotes_current checked⟩ (keptWords + 2)
    (by
      change program.resultType.toCore = _
      rw [typed, choiceType_toCore])

def callContract (plan : CheckedPlan) : CheckedCoreContract :=
  choiceContract plan.callProgram plan.callChecked rfl

def resumeContract (plan : CheckedPlan) : CheckedCoreContract :=
  choiceContract plan.resumeProgram plan.resumeChecked rfl

/-- The parent in continuation-passing form for the choice chain: the call
phase and one resume phase per possible call, all the same program. -/
def parent (plan : CheckedPlan) : CallChoiceParent := {
  call := ⟨plan.callContract, .choose⟩
  resumes := List.replicate maxCalls ⟨plan.resumeContract, .choose⟩
  keptWords := keptWords
  call_entryProfile := rfl
  resumes_entryProfile := by
    intro phase member
    rw [List.eq_of_mem_replicate member]
    rfl
}

theorem childContract_entryProfile (plan : CheckedPlan) :
    plan.childContract.entryProfile = .rawOutcomeV1 2 := rfl

end CheckedPlan
end Solcore.Synthesis.Core.CallBranch
