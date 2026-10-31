import Solcore.ContractRuntime.CallChainExecution

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

/-! ### Every call is the one-call child step -/

theorem resumeFrom_calls_childStep
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List ChoicePhase} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      (∀ call ∈ calls, childStep registry parent call.request call.world fuel = some call.child) →
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      ∀ call ∈ made, childStep registry parent call.request call.world fuel = some call.child := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made _ completed
      cases completed
  | cons phase rest ih =>
      intro index calls request world outcome finalWorld made earlier completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · rename_i child stepped
        have recorded : ∀ call ∈ calls ++ [⟨request, world, child⟩],
            childStep registry parent call.request call.world fuel = some call.child := by
          intro call member
          rcases List.mem_append.mp member with member | member
          · exact earlier call member
          · simp only [List.mem_singleton] at member
            subst member
            exact stepped
        split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · split at completed
              · exact ih recorded completed
              · cases completed
                exact recorded
            · cases completed
              exact recorded
            · cases completed
              exact recorded
        · cases completed

/-- Every call of a completed transaction is the child step of its request in
the world its requesting phase left, so `CallResumeExecution`'s child-step laws
hold for each. -/
theorem run_calls_childStep
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls) :
    ∀ call ∈ calls, childStep registry parent call.request call.world fuel = some call.child := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · split at completed
    · cases completed
      simp
    · cases completed
      simp
    · split at completed
      · exact resumeFrom_calls_childStep (by simp) completed
      · cases completed
        simp

/-- A child that does not return leaves the world its requesting phase left. -/
theorem run_call_world_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    {call : Call} (member : call ∈ calls) (notReturned : call.child.status ≠ .returned) :
    call.child.world = call.world :=
  CallResumeExecution.childStep_world_of_ne_returned (run_calls_childStep completed call member) notReturned

/-- A trapped or failed child delivers no bytes. -/
theorem run_call_data_of_trapped_or_failed
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    {call : Call} (member : call ∈ calls)
    (stopped : call.child.status = .trapped ∨ call.child.status = .failed) :
    call.child.data = ByteArray.empty :=
  CallResumeExecution.childStep_data_of_trapped_or_failed (run_calls_childStep completed call member) stopped

/-! ### The number of calls -/

theorem resumeFrom_calls_length_le
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List ChoicePhase} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      made.length ≤ calls.length + phases.length := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made completed
      cases completed
  | cons phase rest ih =>
      intro index calls request world outcome finalWorld made completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · split at completed
              · have counted := ih completed
                simp only [List.length_append, List.length_cons, List.length_nil] at counted ⊢
                omega
              · cases completed
                simp
            · cases completed
              simp
            · cases completed
              simp
        · cases completed

/-- A completed transaction made at most one call per phase after the call
phase. -/
theorem run_calls_length_le
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls) :
    calls.length ≤ contract.resumes.length := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · split at completed
    · cases completed
      simp
    · cases completed
      simp
    · split at completed
      · have counted := resumeFrom_calls_length_le completed
        simpa using counted
      · cases completed
        simp

/-! ### Root rollback -/

theorem resumeFrom_finalWorld_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List ChoicePhase} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      (∀ data, outcome ≠ .returned data) →
      finalWorld = before := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made completed _
      cases completed
  | cons phase rest ih =>
      intro index calls request world outcome finalWorld made completed notReturned
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · split at completed
              · exact ih completed notReturned
              · cases completed
                exact absurd rfl (notReturned _)
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

/-- A transaction that does not return commits the world before it. -/
theorem run_finalWorld_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    (notReturned : ∀ data, outcome ≠ .returned data) :
    finalWorld = world := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · split at completed
    · cases completed
      rfl
    · cases completed
      rfl
    · split at completed
      · exact resumeFrom_finalWorld_of_ne_returned completed notReturned
      · cases completed
        exact absurd rfl (notReturned _)

/-! ### Balances and the parent's code -/

theorem resumeFrom_balance?
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} (observed : Address) :
    ∀ {phases : List ChoicePhase} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      world.balance? observed = before.balance? observed →
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      finalWorld.balance? observed = before.balance? observed := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made _ completed
      cases completed
  | cons phase rest ih =>
      intro index calls request world outcome finalWorld made kept completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · rename_i child stepped
        split at completed
        · split at completed
          · cases completed
          · cases completed
          · rename_i resumed ranResume
            have resumedKept : resumed.finalWorld.balance? observed = before.balance? observed := by
              rw [CallResumeExecution.phase?_completed_balance? ranResume,
                CallResumeExecution.withCodeAt_balance?,
                CallResumeExecution.childStep_balance? stepped, kept]
            split at completed
            · split at completed
              · exact ih resumedKept completed
              · cases completed
                rw [CallResumeExecution.withCodeAt_balance?, resumedKept]
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

/-- Every account's balance after a completed transaction is the one before. -/
theorem run_balance?
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    (observed : Address) :
    finalWorld.balance? observed = world.balance? observed := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · rename_i called ran
    split at completed
    · cases completed
      rfl
    · cases completed
      rfl
    · split at completed
      · exact resumeFrom_balance? observed (CallResumeExecution.phase?_completed_balance? ran observed) completed
      · cases completed
        rw [CallResumeExecution.withCodeAt_balance?, CallResumeExecution.phase?_completed_balance? ran observed]

theorem resumeFrom_code?
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List ChoicePhase} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      finalWorld = before ∨ finalWorld.code? parent = some contract.call.contract.code := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made completed
      cases completed
  | cons phase rest ih =>
      intro index calls request world outcome finalWorld made completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · rename_i resumed ranResume
            split at completed
            · split at completed
              · exact ih completed
              · cases completed
                exact .inr (CallResumeExecution.withCodeAt_code? _ _ _ resumed.committedDelta.finalAccount_present)
            · cases completed
              exact .inl rfl
            · cases completed
              exact .inl rfl
        · cases completed

/-- The parent's code after a completed transaction is the call phase's, as
before it. -/
theorem run_code?
    {registry : CheckedContractRegistry} {contract : CallChoiceParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls) :
    finalWorld.code? parent = world.code? parent := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · rename_i called ran
    have installedCall : world.code? parent = some contract.call.contract.code := CallResumeExecution.phase?_code? ran
    split at completed
    · cases completed
      rfl
    · cases completed
      rfl
    · split at completed
      · rcases resumeFrom_code? completed with same | restored
        · rw [same]
        · rw [restored, installedCall]
      · cases completed
        have restored : (withCodeAt called.finalWorld parent contract.call.contract.code).code? parent =
            some contract.call.contract.code :=
          CallResumeExecution.withCodeAt_code? _ _ _ called.committedDelta.finalAccount_present
        rw [restored, installedCall]

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
