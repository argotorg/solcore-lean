import Solcore.ContractRuntime.Contracts
import Solcore.Core.Syntax
import Solcore.Core.Primitive
import Solcore.ContractRuntime.RuntimeScalars
import Solcore.ContractRuntime.Internal.ScalarLaws
import Solcore.ContractRuntime.StorageDriver
import Solcore.ContractRuntime.WorldState
import Solcore.ContractRuntime.Frames
import Solcore.ContractRuntime.TopLevel
import Solcore.ContractRuntime.Transactions
import Solcore.Core.HostTyping
import Solcore.Core.Machine
import Solcore.ContractRuntime.Internal.ContractLaws

/-!
# Call phases

A parent contract in continuation-passing form, split at its calls into phases that run at one
address. `CallResumeParent` and `CallResumeExecution.run` make one call, `CallChainParent` and
`CallChainExecution.run` a fixed list, and `CallChoiceParent` and `CallChoiceExecution.run` let the
input decide how many.

Main theorems: `CallChainExecution.toCallResume_run_ofCallResume` says a chain with no middle phases
is the one-call convention, and `CallChoiceExecution.run_ofChain` that a chain is the special case of
request phases and one last finish phase.
-/

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCallResumeExecution
/-! A parent contract in continuation-passing form, split at its one call. The
call phase returns its request as a static tuple: the target, the selector, the
argument and the Words it keeps. The child resolved at the target runs as a
top-level invocation of any convention, with the parent as caller, zero value
and the selector's four bytes and the argument's 32 as its input data. The
resume phase then runs at the parent, with the parent's code swapped for its
own, on the kept Words, the child's status Word and the child's returned or
reverted bytes, which it reads through the input-data requests. Every step goes
through the public top-level runner, and the parent's code is restored on a
return.

The convention commits as one transaction does: a child that does not return
leaves the call phase's world, and a call or resume phase that does not return
commits the world before the transaction. It covers one call at depth one with
zero value and reports no logs. A target that does not resolve fails the call
with no return data, where the EVM answers an account without code with empty
success. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A parent split at its one call into a call phase that returns its request
and a resume phase that reads the child's outcome. -/
structure CallResumeParent where
  call : CheckedCoreContract
  resume : CheckedCoreContract
  /-- The Words the call phase keeps for the resume phase. -/
  keptWords : Nat
  call_entryProfile : call.entryProfile = .wordTupleOutcomeV1 (keptWords + 1)
  resume_entryProfile : resume.entryProfile = .wordOutcomeV1

namespace CallResumeExecution

/-- The step whose fuel ran out, or whose contract was not installed. -/
inductive Stage where
  | call
  | child
  | resume
  deriving Repr, BEq, DecidableEq

/-- How the child's run ended. -/
inductive ChildStatus where
  | returned
  | reverted
  | trapped
  /-- The target is not an address, or no checked contract is installed there. -/
  | failed
  deriving Repr, BEq, DecidableEq

/-- The status Word the resume phase reads. -/
def ChildStatus.word : ChildStatus → Core.Word
  | .returned => Core.Word.ofNatModulo 1
  | .reverted => Core.Word.zero
  | .trapped => Core.Word.ofNatModulo 2
  | .failed => Core.Word.ofNatModulo 3

/-- The call phase's request. -/
structure Request where
  target : Core.Word
  selector : Core.Word
  argument : Core.Word
  kept : List Core.Word
  deriving Repr, BEq

/-- The big-endian Word at Word index `index` of `bytes`. -/
def wordAt (bytes : Bytes) (index : Nat) : Core.Word :=
  (decodeWordBytesBE? (bytes.extract (32 * index) (32 * index + 32))).getD Core.Word.zero

/-- The request in the call phase's returned Words: the target, the selector,
the argument, then the kept Words. -/
def request (keptWords : Nat) (bytes : Bytes) : Request :=
  ⟨wordAt bytes 0, wordAt bytes 1, wordAt bytes 2, (List.range keptWords).map (wordAt bytes <| · + 3)⟩

/-- The selector's four low-order bytes, big-endian. -/
def selectorBytes (selector : Core.Word) : Bytes :=
  (encodeWordBytesBE selector).extract 28 32

/-- The child's input data: the selector's four bytes, then the argument. -/
def childInputBytes (request : Request) : Bytes :=
  selectorBytes request.selector ++ encodeWordBytesBE request.argument

theorem childInputBytes_size (request : Request) : (childInputBytes request).size = 36 := by
  simp [childInputBytes, selectorBytes, ByteArray.size_append, ByteArray.size_extract,
    encodeWordBytesBE_size]

def childInputData (request : Request) : HostStorageDriver.InputData := {
  bytes := childInputBytes request
  size_lt_wordModulus := by
    rw [childInputBytes_size]
    decide
}

/-- The child's invocation: the parent as caller and zero value. -/
def childInvocation (parent target : Address) (request : Request) : TopLevelInvocation := {
  target := target
  caller := parent
  callValue := Core.Word.zero
  inputData := childInputData request
}

/-- The resume phase's input bytes: the kept Words, the status Word, then the
child's returned or reverted bytes. -/
def resumeInputBytes (request : Request) (status : ChildStatus) (data : Bytes) : Bytes :=
  request.kept.foldl (fun bytes word => bytes ++ encodeWordBytesBE word) ByteArray.empty ++
    encodeWordBytesBE status.word ++ data

/-- The child step's status, delivered bytes and world. -/
structure ChildResult where
  status : ChildStatus
  data : Bytes
  world : WorldState

/-- Resolve and run the child: none when its fuel runs out. A returned child
commits its world and delivers its returned bytes; a reverted one delivers its
revert bytes and a trapped or failed one nothing, both in the call phase's
world. -/
def childStep (registry : CheckedContractRegistry) (parent : Address) (request : Request)
    (world : WorldState) (fuel : Nat) : Option ChildResult :=
  match wordToAddress? request.target with
  | none => some ⟨.failed, ByteArray.empty, world⟩
  | some target =>
      match registry.resolve? world target with
      | none => some ⟨.failed, ByteArray.empty, world⟩
      | some ⟨child, installed⟩ =>
          match TopLevelExecution.run child (childInvocation parent target request) installed fuel with
          | .outOfFuel .. => none
          | .completed result =>
              match result.outcome with
              | .returned data => some ⟨.returned, data, result.finalWorld⟩
              | .reverted data => some ⟨.reverted, data, world⟩
              | .trapped _ => some ⟨.trapped, ByteArray.empty, world⟩

/-- Install `code` at `address`, keeping the account's storage, balance and
nonce. -/
def withCodeAt (world : WorldState) (address : Address) (code : CheckedHostCoreProgram) : WorldState :=
  match world.account? address with
  | some account => world.putAccount address (account.withCode code)
  | none => world

/-- One top-level run of `contract`, when its code is installed at the
invocation's target. -/
def phase? (contract : CheckedCoreContract) (world : WorldState) (invocation : TopLevelInvocation)
    (fuel : Nat) : Option (TopLevelRunResult world contract invocation) :=
  match present : world.account? invocation.target with
  | none => none
  | some account =>
      match codeEntry : account.code? with
      | none => none
      | some installedCode =>
          if exactCode : installedCode.program = contract.code.program then
            some (TopLevelExecution.run contract invocation ⟨account, present,
              codeEntry.trans (congrArg some (CheckedHostCoreProgram.eq_of_program_eq exactCode))⟩ fuel)
          else none

/-- One composed transaction. A completion records the request and the child's
result when the call phase returned. -/
inductive Result where
  | completed (outcome : FrameOutcome Core.Word) (finalWorld : WorldState)
      (request : Option Request) (child : Option ChildResult)
  | outOfFuel (stage : Stage)
  | unresolved (stage : Stage)
  /-- The resume phase's input would not fit a Word's size. -/
  | inputLimit

/-- The invocation of the call phase or the resume phase. -/
def parentInvocation (parent caller : Address) (input : HostStorageDriver.InputData) : TopLevelInvocation := {
  target := parent
  caller := caller
  callValue := Core.Word.zero
  inputData := input
}

/-- The resume step over the child's result, in the world the child left. -/
def resumeStep (contract : CallResumeParent) (world : WorldState) (parent caller : Address)
    (request : Request) (child : ChildResult) (fuel : Nat) : Result :=
  if bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus then
    match phase? contract.resume (withCodeAt child.world parent contract.resume.code)
        (parentInvocation parent caller ⟨resumeInputBytes request child.status child.data, bounded⟩) fuel with
    | none => .unresolved .resume
    | some (.outOfFuel ..) => .outOfFuel .resume
    | some (.completed resumed) =>
        match resumed.outcome with
        | .returned data =>
            .completed (.returned data) (withCodeAt resumed.finalWorld parent contract.call.code)
              (some request) (some child)
        | .reverted data => .completed (.reverted data) world (some request) (some child)
        | .trapped reason => .completed (.trapped reason) world (some request) (some child)
  else .inputLimit

/-- Run one transaction of the parent at `parent`, called by `caller` with
`input`, each step with the same fuel. -/
def run (registry : CheckedContractRegistry) (contract : CallResumeParent) (world : WorldState)
    (parent caller : Address) (input : HostStorageDriver.InputData) (fuel : Nat) : Result :=
  match phase? contract.call world (parentInvocation parent caller input) fuel with
  | none => .unresolved .call
  | some (.outOfFuel ..) => .outOfFuel .call
  | some (.completed called) =>
      match called.outcome with
      | .reverted data => .completed (.reverted data) world none none
      | .trapped reason => .completed (.trapped reason) world none none
      | .returned bytes =>
          match childStep registry parent (request contract.keptWords bytes) called.finalWorld fuel with
          | none => .outOfFuel .child
          | some child => resumeStep contract world parent caller (request contract.keptWords bytes) child fuel

end CallResumeExecution

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCallChainExecution
/-! A parent contract in continuation-passing form, split at its calls: a call
phase, then one resume phase per call. The call phase returns the first request
as for `CallResumeExecution`, and each request's child runs as its child step.
Each resume phase then runs at the parent, with the parent's code swapped for
its own, on the kept Words, the child's status Word and the child's returned or
reverted bytes, which it reads through the input-data requests. Every resume
phase but the last, a middle phase, returns the next request, which issues the
next call; the last phase's outcome is the transaction's. Every step goes
through the public top-level runner, and the call phase's code is restored on a
return.

The chain commits as one transaction does: a child that does not return leaves
the world of the phase that requested it, and a phase that does not return
commits the world before the transaction. It covers calls at depth one with zero
value and reports no logs. Without middle phases it is `CallResumeExecution`,
whose result `Result.toCallResume` recovers. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- A parent split at its calls into a call phase that returns the first
request, middle phases that read a call's outcome and return the next request,
and a last phase that reads the last call's outcome. -/
structure CallChainParent where
  call : CheckedCoreContract
  /-- The resume phases that issue the next call, in order. -/
  middles : List CheckedCoreContract
  last : CheckedCoreContract
  /-- The Words each requesting phase keeps for the next phase. -/
  keptWords : Nat
  call_entryProfile : call.entryProfile = .wordTupleOutcomeV1 (keptWords + 1)
  middles_entryProfile : ∀ phase ∈ middles, phase.entryProfile = .wordTupleOutcomeV1 (keptWords + 1)
  last_entryProfile : last.entryProfile = .wordOutcomeV1

namespace CallChainExecution

open CallResumeExecution (Request ChildResult childStep resumeInputBytes phase? withCodeAt
  parentInvocation)

/-- The step whose fuel ran out, or whose contract was not installed. Calls
count from zero. -/
inductive Stage where
  | call
  /-- The child of call `index`. -/
  | child (index : Nat)
  /-- The resume phase after call `index`. -/
  | resume (index : Nat)
  deriving Repr, BEq, DecidableEq

/-- One call: its request, the world its requesting phase left, in which the
child step ran, and the child's result. -/
structure Call where
  request : Request
  world : WorldState
  child : ChildResult

/-- One composed transaction. A completion records every call made, in order. -/
inductive Result where
  | completed (outcome : FrameOutcome Core.Word) (finalWorld : WorldState) (calls : List Call)
  | outOfFuel (stage : Stage)
  | unresolved (stage : Stage)
  /-- The input of the resume phase after call `index` would not fit a Word's size. -/
  | inputLimit (index : Nat)

/-- The call of `request` in `world`, as call `index` after `calls`, then the
resume phases `phases` from there: a middle phase while one remains, else the
last. `before` is the world before the transaction. -/
def resumeFrom (registry : CheckedContractRegistry) (contract : CallChainParent)
    (before : WorldState) (parent caller : Address) (fuel : Nat) :
    List CheckedCoreContract → Nat → List Call → Request → WorldState → Result
  | [], index, calls, request, world =>
      match childStep registry parent request world fuel with
      | none => .outOfFuel (.child index)
      | some child =>
          if bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus then
            match phase? contract.last (withCodeAt child.world parent contract.last.code)
                (parentInvocation parent caller ⟨resumeInputBytes request child.status child.data, bounded⟩)
                fuel with
            | none => .unresolved (.resume index)
            | some (.outOfFuel ..) => .outOfFuel (.resume index)
            | some (.completed resumed) =>
                match resumed.outcome with
                | .returned data =>
                    .completed (.returned data) (withCodeAt resumed.finalWorld parent contract.call.code)
                      (calls ++ [⟨request, world, child⟩])
                | .reverted data => .completed (.reverted data) before (calls ++ [⟨request, world, child⟩])
                | .trapped reason => .completed (.trapped reason) before (calls ++ [⟨request, world, child⟩])
          else .inputLimit index
  | middle :: rest, index, calls, request, world =>
      match childStep registry parent request world fuel with
      | none => .outOfFuel (.child index)
      | some child =>
          if bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus then
            match phase? middle (withCodeAt child.world parent middle.code)
                (parentInvocation parent caller ⟨resumeInputBytes request child.status child.data, bounded⟩)
                fuel with
            | none => .unresolved (.resume index)
            | some (.outOfFuel ..) => .outOfFuel (.resume index)
            | some (.completed resumed) =>
                match resumed.outcome with
                | .returned bytes =>
                    resumeFrom registry contract before parent caller fuel rest (index + 1)
                      (calls ++ [⟨request, world, child⟩])
                      (CallResumeExecution.request contract.keptWords bytes) resumed.finalWorld
                | .reverted data => .completed (.reverted data) before (calls ++ [⟨request, world, child⟩])
                | .trapped reason => .completed (.trapped reason) before (calls ++ [⟨request, world, child⟩])
          else .inputLimit index

/-- Run one transaction of the parent at `parent`, called by `caller` with
`input`, each step with the same fuel. -/
def run (registry : CheckedContractRegistry) (contract : CallChainParent) (world : WorldState)
    (parent caller : Address) (input : HostStorageDriver.InputData) (fuel : Nat) : Result :=
  match phase? contract.call world (parentInvocation parent caller input) fuel with
  | none => .unresolved .call
  | some (.outOfFuel ..) => .outOfFuel .call
  | some (.completed called) =>
      match called.outcome with
      | .reverted data => .completed (.reverted data) world []
      | .trapped reason => .completed (.trapped reason) world []
      | .returned bytes =>
          resumeFrom registry contract world parent caller fuel contract.middles 0 []
            (CallResumeExecution.request contract.keptWords bytes) called.finalWorld

/-! ### The one-call convention -/

/-- The one-call parent as a chain without middle phases. -/
def ofCallResume (contract : CallResumeParent) : CallChainParent where
  call := contract.call
  middles := []
  last := contract.resume
  keptWords := contract.keptWords
  call_entryProfile := contract.call_entryProfile
  middles_entryProfile := by simp
  last_entryProfile := contract.resume_entryProfile

/-- A chain's result as a one-call result: its first call's request and child,
which are its only call's without middle phases. -/
def Result.toCallResume : Result → CallResumeExecution.Result
  | .completed outcome finalWorld [] => .completed outcome finalWorld none none
  | .completed outcome finalWorld (call :: _) => .completed outcome finalWorld (some call.request) (some call.child)
  | .outOfFuel .call => .outOfFuel .call
  | .outOfFuel (.child _) => .outOfFuel .child
  | .outOfFuel (.resume _) => .outOfFuel .resume
  | .unresolved .call => .unresolved .call
  | .unresolved (.child _) => .unresolved .child
  | .unresolved (.resume _) => .unresolved .resume
  | .inputLimit _ => .inputLimit

/-- Without middle phases the chain is the one-call convention. -/
theorem toCallResume_run_ofCallResume
    (registry : CheckedContractRegistry) (contract : CallResumeParent) (world : WorldState)
    (parent caller : Address) (input : HostStorageDriver.InputData) (fuel : Nat) :
    (run registry (ofCallResume contract) world parent caller input fuel).toCallResume =
      CallResumeExecution.run registry contract world parent caller input fuel := by
  unfold run CallResumeExecution.run
  dsimp only [ofCallResume]
  generalize phase? contract.call world (parentInvocation parent caller input) fuel = ran
  rcases ran with _ | (called | _)
  · rfl
  · dsimp only
    generalize called.outcome = outcome
    rcases outcome with bytes | data | reason
    · dsimp only
      unfold resumeFrom CallResumeExecution.resumeStep
      generalize childStep registry parent (CallResumeExecution.request contract.keptWords bytes)
        called.finalWorld fuel = stepped
      rcases stepped with _ | child
      · rfl
      · dsimp only
        by_cases bounded : (resumeInputBytes (CallResumeExecution.request contract.keptWords bytes)
            child.status child.data).size < Core.wordModulus
        · rw [dif_pos bounded, dif_pos bounded]
          generalize phase? contract.resume (withCodeAt child.world parent contract.resume.code)
            (parentInvocation parent caller ⟨_, bounded⟩) fuel = resumedRun
          rcases resumedRun with _ | (resumed | _)
          · rfl
          · dsimp only
            generalize resumed.outcome = last
            rcases last with returned | reverted | reason <;> rfl
          · rfl
        · rw [dif_neg bounded, dif_neg bounded]
          rfl
    · rfl
    · rfl
  · rfl

end CallChainExecution

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.Internal.DefsCallChoiceExecution
/-! A parent contract in continuation-passing form whose phases may each either
request a call or finish, so that the input decides how many calls a
transaction makes. The call phase is installed as the parent's code and runs
first; the phase after call `index` is `resumes[index]`. Every phase has a role:
a request phase always returns the next request and a finish phase always ends
the transaction, as the call chain's phases do, while a choice phase returns a
tuple whose first Word chooses. A zero Word finishes the transaction with the
tuple's second Word as its returned Word; any other Word requests the call that
the remaining Words name, the target, the selector, the argument and the kept
Words. Each request's child runs as `CallResumeExecution`'s child step and each
later phase as its resume phase, on the kept Words, the child's status Word and
the child's returned or reverted bytes. Every step goes through the public
top-level runner, and the call phase's code is restored on a return.

It commits as the call chain does: a child that does not return leaves the
world of the phase that requested it, and a phase that does not return commits
the world before the transaction. A request with no phase left to resume after
it stops the transaction. It covers calls at depth one with zero value and
reports no logs. With request phases and one last finish phase it is
`CallChainExecution`, which `run_ofChain` states. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime

/-- How a returned phase continues the transaction. -/
inductive PhaseRole where
  /-- It requests the next call, as a call or middle phase of the call chain. -/
  | request
  /-- Its outcome is the transaction's, as the call chain's last phase. -/
  | finish
  /-- Its first Word chooses: zero finishes with the second Word as the
  transaction's returned Word, and any other Word requests the call that the
  following Words name. -/
  | choose
  deriving Repr, BEq, DecidableEq

/-- The convention of a phase in each role, for `keptWords` kept Words: a
request carries the target, the selector, the argument and the kept Words, and a
choice one Word more before them. -/
def PhaseRole.entryProfile (keptWords : Nat) : PhaseRole → CoreContractEntryProfile
  | .request => .wordTupleOutcomeV1 (keptWords + 1)
  | .finish => .wordOutcomeV1
  | .choose => .wordTupleOutcomeV1 (keptWords + 2)

/-- One phase of a parent and its role. -/
structure ChoicePhase where
  contract : CheckedCoreContract
  role : PhaseRole

/-- A parent split at its calls into a call phase and the phases that resume
after each call, each in its role. -/
structure CallChoiceParent where
  call : ChoicePhase
  /-- The phase after call `index` is `resumes[index]`. -/
  resumes : List ChoicePhase
  /-- The Words each requesting phase keeps for the next phase. -/
  keptWords : Nat
  call_entryProfile : call.contract.entryProfile = call.role.entryProfile keptWords
  resumes_entryProfile : ∀ phase ∈ resumes, phase.contract.entryProfile = phase.role.entryProfile keptWords

namespace CallChoiceExecution

open CallResumeExecution (Request ChildResult childStep resumeInputBytes phase? withCodeAt
  parentInvocation wordAt)

open CallChainExecution (Stage Call)

/-- What a returned phase asks for. -/
inductive Next where
  | call (request : Request)
  | finish (data : Bytes)

/-- A returned phase's next step in its role, from its returned bytes. -/
def next (keptWords : Nat) : PhaseRole → Bytes → Next
  | .request, bytes => .call (CallResumeExecution.request keptWords bytes)
  | .finish, bytes => .finish bytes
  | .choose, bytes =>
      if wordAt bytes 0 = Core.Word.zero then .finish (encodeWordBytesBE (wordAt bytes 1))
      else .call (CallResumeExecution.request keptWords (bytes.extract 32 bytes.size))

/-- One composed transaction. A completion records every call made, in order. -/
inductive Result where
  | completed (outcome : FrameOutcome Core.Word) (finalWorld : WorldState) (calls : List Call)
  | outOfFuel (stage : Stage)
  | unresolved (stage : Stage)
  /-- The input of the phase after call `index` would not fit a Word's size. -/
  | inputLimit (index : Nat)
  /-- Call `index` was requested with no phase left to resume after it. -/
  | callLimit (index : Nat)

/-- The call of `request` in `world`, as call `index` after `calls`, then the
phases `phases` from there. `before` is the world before the transaction. -/
def resumeFrom (registry : CheckedContractRegistry) (contract : CallChoiceParent)
    (before : WorldState) (parent caller : Address) (fuel : Nat) :
    List ChoicePhase → Nat → List Call → Request → WorldState → Result
  | [], index, _, _, _ => .callLimit index
  | phase :: rest, index, calls, request, world =>
      match childStep registry parent request world fuel with
      | none => .outOfFuel (.child index)
      | some child =>
          if bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus then
            match phase? phase.contract (withCodeAt child.world parent phase.contract.code)
                (parentInvocation parent caller ⟨resumeInputBytes request child.status child.data, bounded⟩)
                fuel with
            | none => .unresolved (.resume index)
            | some (.outOfFuel ..) => .outOfFuel (.resume index)
            | some (.completed resumed) =>
                match resumed.outcome with
                | .returned bytes =>
                    match next contract.keptWords phase.role bytes with
                    | .call following =>
                        resumeFrom registry contract before parent caller fuel rest (index + 1)
                          (calls ++ [⟨request, world, child⟩]) following resumed.finalWorld
                    | .finish data =>
                        .completed (.returned data) (withCodeAt resumed.finalWorld parent contract.call.contract.code)
                          (calls ++ [⟨request, world, child⟩])
                | .reverted data => .completed (.reverted data) before (calls ++ [⟨request, world, child⟩])
                | .trapped reason => .completed (.trapped reason) before (calls ++ [⟨request, world, child⟩])
          else .inputLimit index

/-- Run one transaction of the parent at `parent`, called by `caller` with
`input`, each step with the same fuel. -/
def run (registry : CheckedContractRegistry) (contract : CallChoiceParent) (world : WorldState)
    (parent caller : Address) (input : HostStorageDriver.InputData) (fuel : Nat) : Result :=
  match phase? contract.call.contract world (parentInvocation parent caller input) fuel with
  | none => .unresolved .call
  | some (.outOfFuel ..) => .outOfFuel .call
  | some (.completed called) =>
      match called.outcome with
      | .reverted data => .completed (.reverted data) world []
      | .trapped reason => .completed (.trapped reason) world []
      | .returned bytes =>
          match next contract.keptWords contract.call.role bytes with
          | .call request =>
              resumeFrom registry contract world parent caller fuel contract.resumes 0 [] request called.finalWorld
          | .finish data => .completed (.returned data) (withCodeAt called.finalWorld parent contract.call.contract.code) []

/-! ### The call chain -/

/-- The call chain as request phases and one last finish phase. -/
def ofChain (contract : CallChainParent) : CallChoiceParent where
  call := ⟨contract.call, .request⟩
  resumes := contract.middles.map (fun middle => ⟨middle, .request⟩) ++ [⟨contract.last, .finish⟩]
  keptWords := contract.keptWords
  call_entryProfile := contract.call_entryProfile
  resumes_entryProfile := by
    intro phase member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨middle, inMiddles, rfl⟩ := List.mem_map.mp member
      exact contract.middles_entryProfile middle inMiddles
    · simp only [List.mem_singleton] at member
      subst member
      exact contract.last_entryProfile

/-- A call-chain result as a result of this convention. -/
def _root_.Solcore.ContractRuntime.CallChainExecution.Result.toChoice : CallChainExecution.Result → Result
  | .completed outcome finalWorld calls => .completed outcome finalWorld calls
  | .outOfFuel stage => .outOfFuel stage
  | .unresolved stage => .unresolved stage
  | .inputLimit index => .inputLimit index

theorem resumeFrom_ofChain (registry : CheckedContractRegistry) (contract : CallChainParent)
    (before : WorldState) (parent caller : Address) (fuel : Nat) :
    ∀ (middles : List CheckedCoreContract) (index : Nat) (calls : List Call) (request : Request)
      (world : WorldState),
      resumeFrom registry (ofChain contract) before parent caller fuel
          (middles.map (fun middle => ⟨middle, .request⟩) ++ [⟨contract.last, .finish⟩]) index calls request world =
        (CallChainExecution.resumeFrom registry contract before parent caller fuel middles index calls request
          world).toChoice := by
  intro middles
  induction middles with
  | nil =>
      intro index calls request world
      simp only [List.map_nil, List.nil_append]
      unfold resumeFrom CallChainExecution.resumeFrom
      generalize childStep registry parent request world fuel = stepped
      rcases stepped with _ | child
      · rfl
      · dsimp only
        by_cases bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus
        · rw [dif_pos bounded, dif_pos bounded]
          generalize phase? contract.last (withCodeAt child.world parent contract.last.code)
            (parentInvocation parent caller ⟨_, bounded⟩) fuel = resumedRun
          rcases resumedRun with _ | (resumed | _)
          · rfl
          · dsimp only
            generalize resumed.outcome = last
            rcases last with returned | reverted | reason <;> rfl
          · rfl
        · rw [dif_neg bounded, dif_neg bounded]
          rfl
  | cons middle rest ih =>
      intro index calls request world
      simp only [List.map_cons, List.cons_append]
      unfold resumeFrom CallChainExecution.resumeFrom
      generalize childStep registry parent request world fuel = stepped
      rcases stepped with _ | child
      · rfl
      · dsimp only
        by_cases bounded : (resumeInputBytes request child.status child.data).size < Core.wordModulus
        · rw [dif_pos bounded, dif_pos bounded]
          generalize phase? middle (withCodeAt child.world parent middle.code)
            (parentInvocation parent caller ⟨_, bounded⟩) fuel = resumedRun
          rcases resumedRun with _ | (resumed | _)
          · rfl
          · dsimp only
            generalize resumed.outcome = outcome
            rcases outcome with returned | reverted | reason
            · exact ih _ _ _ _
            · rfl
            · rfl
          · rfl
        · rw [dif_neg bounded, dif_neg bounded]
          rfl

/-- The call chain is the special case of request phases and one last finish
phase. -/
theorem run_ofChain (registry : CheckedContractRegistry) (contract : CallChainParent) (world : WorldState)
    (parent caller : Address) (input : HostStorageDriver.InputData) (fuel : Nat) :
    run registry (ofChain contract) world parent caller input fuel =
      (CallChainExecution.run registry contract world parent caller input fuel).toChoice := by
  unfold run CallChainExecution.run
  dsimp only [ofChain]
  generalize phase? contract.call world (parentInvocation parent caller input) fuel = ran
  rcases ran with _ | (called | _)
  · rfl
  · dsimp only
    generalize called.outcome = outcome
    rcases outcome with bytes | data | reason
    · exact resumeFrom_ofChain registry contract world parent caller fuel contract.middles 0 [] _ _
    · rfl
    · rfl
  · rfl

end CallChoiceExecution

end Solcore.ContractRuntime
end
