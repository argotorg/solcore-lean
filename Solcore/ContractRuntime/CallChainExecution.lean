import Solcore.ContractRuntime.CallResumeExecution

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

/-! ### Every call is the one-call child step -/

/-- Each call recorded after `calls` is the child step of its request in the
world its requesting phase left. -/
theorem resumeFrom_calls_childStep
    {registry : CheckedContractRegistry} {contract : CallChainParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List CheckedCoreContract} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      (∀ call ∈ calls, childStep registry parent call.request call.world fuel = some call.child) →
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      ∀ call ∈ made, childStep registry parent call.request call.world fuel = some call.child := by
  intro phases
  induction phases with
  | nil =>
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
          · split at completed <;> (cases completed; exact recorded)
        · cases completed
  | cons middle rest ih =>
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
            · exact ih recorded completed
            · cases completed
              exact recorded
            · cases completed
              exact recorded
        · cases completed

/-- Every call of a completed transaction is the child step of its request in
the world its requesting phase left, so `CallResumeExecution`'s child-step laws
hold for each: a child that does not return leaves that world, a trapped or
failed child delivers nothing, and a resolved child delivers its outcome as the
public top-level runner reports it. -/
theorem run_calls_childStep
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
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
    · exact resumeFrom_calls_childStep (by simp) completed

/-- A child that does not return leaves the world its requesting phase left. -/
theorem run_call_world_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    {call : Call} (member : call ∈ calls) (notReturned : call.child.status ≠ .returned) :
    call.child.world = call.world :=
  CallResumeExecution.childStep_world_of_ne_returned (run_calls_childStep completed call member) notReturned

/-- A trapped or failed child delivers no bytes. -/
theorem run_call_data_of_trapped_or_failed
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls)
    {call : Call} (member : call ∈ calls)
    (stopped : call.child.status = .trapped ∨ call.child.status = .failed) :
    call.child.data = ByteArray.empty :=
  CallResumeExecution.childStep_data_of_trapped_or_failed (run_calls_childStep completed call member) stopped

/-! ### The number of calls -/

theorem resumeFrom_calls_length_of_returned
    {registry : CheckedContractRegistry} {contract : CallChainParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List CheckedCoreContract} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {data : Bytes} {finalWorld : WorldState} {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed (.returned data) finalWorld made →
      made.length = calls.length + phases.length + 1 := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world data finalWorld made completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · cases completed
              simp
            · cases completed
            · cases completed
        · cases completed
  | cons middle rest ih =>
      intro index calls request world data finalWorld made completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · have counted := ih completed
              simp only [List.length_append, List.length_cons, List.length_nil] at counted ⊢
              omega
            · cases completed
            · cases completed
        · cases completed

/-- A returned transaction made one call more than there are middle phases. -/
theorem run_calls_length_of_returned
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {data : Bytes} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed (.returned data) finalWorld calls) :
    calls.length = contract.middles.length + 1 := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · split at completed
    · cases completed
    · cases completed
    · have counted := resumeFrom_calls_length_of_returned completed
      simpa using counted

/-! ### Root rollback -/

theorem resumeFrom_finalWorld_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChainParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List CheckedCoreContract} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      (∀ data, outcome ≠ .returned data) →
      finalWorld = before := by
  intro phases
  induction phases with
  | nil =>
      intro index calls request world outcome finalWorld made completed notReturned
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · cases completed
              exact absurd rfl (notReturned _)
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed
  | cons middle rest ih =>
      intro index calls request world outcome finalWorld made completed notReturned
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · exact ih completed notReturned
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

/-- A transaction that does not return commits the world before it. -/
theorem run_finalWorld_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
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
    · exact resumeFrom_finalWorld_of_ne_returned completed notReturned

/-! ### Balances and the parent's code -/

theorem resumeFrom_balance?
    {registry : CheckedContractRegistry} {contract : CallChainParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} (observed : Address) :
    ∀ {phases : List CheckedCoreContract} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      world.balance? observed = before.balance? observed →
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      finalWorld.balance? observed = before.balance? observed := by
  intro phases
  induction phases with
  | nil =>
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
            split at completed
            · cases completed
              rw [CallResumeExecution.withCodeAt_balance?,
                CallResumeExecution.phase?_completed_balance? ranResume,
                CallResumeExecution.withCodeAt_balance?,
                CallResumeExecution.childStep_balance? stepped, kept]
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed
  | cons middle rest ih =>
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
            split at completed
            · apply ih _ completed
              rw [CallResumeExecution.phase?_completed_balance? ranResume,
                CallResumeExecution.withCodeAt_balance?,
                CallResumeExecution.childStep_balance? stepped, kept]
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

/-- Every account's balance after a completed transaction is the one before. -/
theorem run_balance?
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
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
    · exact resumeFrom_balance? observed (CallResumeExecution.phase?_completed_balance? ran observed) completed

theorem resumeFrom_code?
    {registry : CheckedContractRegistry} {contract : CallChainParent} {before : WorldState}
    {parent caller : Address} {fuel : Nat} :
    ∀ {phases : List CheckedCoreContract} {index : Nat} {calls : List Call} {request : Request}
      {world : WorldState} {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
      {made : List Call},
      resumeFrom registry contract before parent caller fuel phases index calls request world =
        .completed outcome finalWorld made →
      finalWorld = before ∨ finalWorld.code? parent = some contract.call.code := by
  intro phases
  induction phases with
  | nil =>
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
            · cases completed
              exact .inr (CallResumeExecution.withCodeAt_code? _ _ _ resumed.committedDelta.finalAccount_present)
            · cases completed
              exact .inl rfl
            · cases completed
              exact .inl rfl
        · cases completed
  | cons middle rest ih =>
      intro index calls request world outcome finalWorld made completed
      unfold resumeFrom at completed
      split at completed
      · cases completed
      · split at completed
        · split at completed
          · cases completed
          · cases completed
          · split at completed
            · exact ih completed
            · cases completed
              exact .inl rfl
            · cases completed
              exact .inl rfl
        · cases completed

/-- The parent's code after a completed transaction is the call phase's, as
before it. -/
theorem run_code?
    {registry : CheckedContractRegistry} {contract : CallChainParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState} {calls : List Call}
    (completed : run registry contract world parent caller input fuel = .completed outcome finalWorld calls) :
    finalWorld.code? parent = world.code? parent := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · rename_i called ran
    have installedCall : world.code? parent = some contract.call.code := CallResumeExecution.phase?_code? ran
    split at completed
    · cases completed
      rfl
    · cases completed
      rfl
    · rcases resumeFrom_code? completed with same | restored
      · rw [same]
      · rw [restored, installedCall]

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
