import Solcore.ContractRuntime.CallPhases
import Solcore.ContractRuntime.Internal.TopLevelLaws
import Solcore.ContractRuntime.Internal.ContractLaws
import Solcore.ContractRuntime.Internal.EntryOutcomeLaws
import Solcore.ContractRuntime.Internal.WorldStateDeltaLaws
import Solcore.ContractRuntime.Internal.ScalarLaws

/-!
# Laws of the call phases

What a call-phase run does to balances, code and the final world.
-/

section
-- leanmerge: from Solcore.ContractRuntime.CallResumeExecution
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

namespace CallResumeExecution

/-! ### The child's invocation and the delivered bytes -/

@[simp] theorem childInvocation_target (parent target : Address) (request : Request) :
    (childInvocation parent target request).target = target := rfl

@[simp] theorem childInvocation_caller (parent target : Address) (request : Request) :
    (childInvocation parent target request).caller = parent := rfl

@[simp] theorem childInvocation_callValue (parent target : Address) (request : Request) :
    (childInvocation parent target request).callValue = Core.Word.zero := rfl

@[simp] theorem childInvocation_inputBytes (parent target : Address) (request : Request) :
    (childInvocation parent target request).inputData.bytes =
      selectorBytes request.selector ++ encodeWordBytesBE request.argument := rfl

/-- A resolved child delivers its outcome exactly as the public top-level runner
reports it: its returned bytes with its world, or its revert bytes in the call
phase's world, or nothing after a trap. -/
theorem childStep_of_completed
    (registry : CheckedContractRegistry) (parent : Address) (request : Request)
    (world : WorldState) (fuel : Nat) {target : Address}
    {child : CheckedCoreContract}
    {installed : InstalledCheckedCoreContract world target child}
    (address : wordToAddress? request.target = some target)
    (resolved : registry.resolve? world target = some ⟨child, installed⟩)
    {result : TopLevelTerminalResult world target}
    (completed :
      TopLevelExecution.run child (childInvocation parent target request) installed fuel =
        .completed result) :
    childStep registry parent request world fuel = some (match result.outcome with
      | .returned data => ⟨.returned, data, result.finalWorld⟩
      | .reverted data => ⟨.reverted, data, world⟩
      | .trapped _ => ⟨.trapped, ByteArray.empty, world⟩) := by
  unfold childStep
  rw [address]
  dsimp only
  rw [resolved]
  dsimp only
  rw [completed]
  dsimp only
  split <;> next _ _ outcomeEq => simp [outcomeEq]

/-- A child that does not return leaves the call phase's world. -/
theorem childStep_world_of_ne_returned
    {registry : CheckedContractRegistry} {parent : Address} {request : Request}
    {world : WorldState} {fuel : Nat} {child : ChildResult}
    (stepped : childStep registry parent request world fuel = some child)
    (notReturned : child.status ≠ .returned) :
    child.world = world := by
  unfold childStep at stepped
  split at stepped
  · cases stepped
    rfl
  · split at stepped
    · cases stepped
      rfl
    · split at stepped
      · cases stepped
      · split at stepped
        · cases stepped
          exact absurd rfl notReturned
        · cases stepped
          rfl
        · cases stepped
          rfl

/-- Only a returned or reverted child delivers bytes. -/
theorem childStep_data_of_trapped_or_failed
    {registry : CheckedContractRegistry} {parent : Address} {request : Request}
    {world : WorldState} {fuel : Nat} {child : ChildResult}
    (stepped : childStep registry parent request world fuel = some child)
    (stopped : child.status = .trapped ∨ child.status = .failed) :
    child.data = ByteArray.empty := by
  unfold childStep at stepped
  split at stepped
  · cases stepped
    rfl
  · split at stepped
    · cases stepped
      rfl
    · split at stepped
      · cases stepped
      · split at stepped
        · cases stepped
          simp at stopped
        · cases stepped
          simp at stopped
        · cases stepped
          rfl

/-- The resume phase reads the kept Words, the status Word and the child's
delivered bytes. -/
@[simp] theorem resumeInputBytes_eq (request : Request) (status : ChildStatus) (data : Bytes) :
    resumeInputBytes request status data =
      request.kept.foldl (fun bytes word => bytes ++ encodeWordBytesBE word) ByteArray.empty ++
        encodeWordBytesBE status.word ++ data := rfl

/-! ### Root rollback -/

/-- A transaction that does not return commits the world before it. -/
theorem run_finalWorld_of_ne_returned
    {registry : CheckedContractRegistry} {contract : CallResumeParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
    {requested : Option Request} {childResult : Option ChildResult}
    (completed : run registry contract world parent caller input fuel =
      .completed outcome finalWorld requested childResult)
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
      · cases completed
      · unfold resumeStep at completed
        split at completed
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

/-! ### Balances and the parent's code -/

theorem withCodeAt_balance? (world : WorldState) (address : Address) (code : CheckedHostCoreProgram)
    (observed : Address) :
    (withCodeAt world address code).balance? observed = world.balance? observed := by
  unfold withCodeAt
  split
  · rename_i account present
    by_cases same : observed = address
    · subst same
      simp [WorldState.balance?, WorldState.account?_putAccount_same, present]
    · simp [WorldState.balance?, WorldState.account?_putAccount_other _ _ _ _ same]
  · rfl

theorem withCodeAt_code? (world : WorldState) (address : Address) (code : CheckedHostCoreProgram)
    {account : Account} (present : world.account? address = some account) :
    (withCodeAt world address code).code? address = some code := by
  simp [withCodeAt, present, WorldState.code?, WorldState.account?_putAccount_same]

theorem withCodeAt_account?_isSome (world : WorldState) (address : Address)
    (code : CheckedHostCoreProgram) (observed : Address) :
    ((withCodeAt world address code).account? observed).isSome =
      (world.account? observed).isSome := by
  unfold withCodeAt
  split
  · rename_i account present
    by_cases same : observed = address
    · subst same
      simp [WorldState.account?_putAccount_same, present]
    · simp [WorldState.account?_putAccount_other _ _ _ _ same]
  · rfl

end CallResumeExecution

namespace FrameCheckpointedWorkingPairWithPresentStorageAccount

universe u v

/-- A storage write keeps the balance at every working-state address. -/
@[simp] theorem workingBalance?_writeStorage
    {RollbackState : Type u}
    {TraceState : Type v}
    (context :
      FrameCheckpointedWorkingPairWithPresentStorageAccount
        RollbackState TraceState)
    (slot value : Core.Word)
    (address : Address) :
    (context.writeStorage slot value).context.values.working.1.balance? address =
      context.context.values.working.1.balance? address := by
  change
    ((context.context.values.working.1.putAccount
        context.context.storageAddress
        (context.storageAccount.storageWrite slot value)).account?
      address).bind (fun account => some account.balance) =
    (context.context.values.working.1.account? address).bind
      (fun account => some account.balance)
  by_cases same : address = context.context.storageAddress
  · subst address
    rw [WorldState.account?_putAccount_same, context.storageAccount_present]
    simp
  · rw [WorldState.account?_putAccount_other _ _ _ _ same]

end FrameCheckpointedWorkingPairWithPresentStorageAccount

namespace TransactionHostStorageDriver

/-- Transaction execution never changes a balance of the working world. -/
@[simp] theorem run_workingBalance?
    (context : Context)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat)
    (state : Core.State)
    (observedAddress : Address) :
    (run context inputs fuel state).context.context.values.working.1.balance?
        observedAddress =
      context.context.values.working.1.balance? observedAddress := by
  simpa only [run] using
    HostDriver.run_observe (handler inputs)
      (fun current =>
        current.context.values.working.1.balance? observedAddress)
      (by
        intro current request
        cases request <;>
          simp [handler, handleRequest, HostStorageDriver.handleRequest] <;> rfl)
      context fuel state

end TransactionHostStorageDriver

namespace TopLevelExecution

/-- The raw run's working world keeps every balance of the initial world. -/
theorem rawRun_working_balance?
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat) (observed : Address) :
    (rawRun contract invocation installed fuel).context.context.values.working.1.balance? observed =
      initialWorld.balance? observed := by
  simp [rawRun, CheckedHostCoreProgram.runWithTransactionStorage]

/-- A completed run commits the raw run's working world on a return and its
initial world otherwise. -/
theorem run_completed_finalWorld
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat)
    {result : TopLevelTerminalResult initialWorld invocation.target}
    (completed : run contract invocation installed fuel = .completed result) :
    result.finalWorld = (match result.outcome with
      | .returned _ => (rawRun contract invocation installed fuel).context.context.values.working.1
      | _ => initialWorld) := by
  cases prefixEq : validatedRawRun contract invocation installed fuel with
  | mk raw resultTyping resultSupported storageAddress_eq delta checkpointJournal_eq =>
      have rawEq : rawRun contract invocation installed fuel = raw := by
        simpa [validatedRawRun] using congrArg ValidatedRawResult.result prefixEq
      cases raw with
      | mk context outcome =>
          cases outcome with
          | done value store =>
              unfold run at completed
              rw [prefixEq] at completed
              unfold classifyRawResult at completed
              dsimp only [ValidatedRawResult.result, ValidatedRawResult.workingDelta] at completed
              split at completed
              · rename_i decoded decodedEq
                cases completed
                rw [rawEq]
                cases decoded <;> simp [finalize]
              · rename_i decodedEq
                have decodedNeNone : contract.decodeCompletion? value ≠ none := by
                  obtain ⟨_world, _storeTyping, valueTyping⟩ := resultTyping
                  apply contract.entryProfile.decode?_ne_none_of_hasType
                  rw [← contract.resultType_eq]
                  exact valueTyping
                exact False.elim (decodedNeNone decodedEq)
          | outOfFuel exhausted =>
              unfold run at completed
              rw [prefixEq] at completed
              unfold classifyRawResult at completed
              dsimp only [ValidatedRawResult.result] at completed
              cases completed
          | fault error faultState =>
              exact False.elim resultTyping
          | unsupported suspension remainingFuel =>
              exact False.elim (resultSupported suspension remainingFuel rfl)

/-- A completed run keeps every balance of its initial world. -/
theorem run_completed_balance?
    {initialWorld : WorldState}
    (contract : CheckedCoreContract)
    (invocation : TopLevelInvocation)
    (installed :
      InstalledCheckedCoreContract initialWorld invocation.target contract)
    (fuel : Nat)
    {result : TopLevelTerminalResult initialWorld invocation.target}
    (completed : run contract invocation installed fuel = .completed result)
    (observed : Address) :
    result.finalWorld.balance? observed = initialWorld.balance? observed := by
  rw [run_completed_finalWorld contract invocation installed fuel completed]
  split
  · exact rawRun_working_balance? contract invocation installed fuel observed
  · rfl

end TopLevelExecution

namespace CallResumeExecution

/-- A phase that runs is the public top-level run of its installed contract. -/
theorem phase?_eq_some
    {contract : CheckedCoreContract} {world : WorldState} {invocation : TopLevelInvocation}
    {fuel : Nat} {result : TopLevelRunResult world contract invocation}
    (ran : phase? contract world invocation fuel = some result) :
    ∃ installed : InstalledCheckedCoreContract world invocation.target contract,
      TopLevelExecution.run contract invocation installed fuel = result := by
  unfold phase? at ran
  split at ran
  · cases ran
  · split at ran
    · cases ran
    · split at ran
      · exact ⟨_, Option.some.inj ran⟩
      · cases ran

theorem phase?_code?
    {contract : CheckedCoreContract} {world : WorldState} {invocation : TopLevelInvocation}
    {fuel : Nat} {result : TopLevelRunResult world contract invocation}
    (ran : phase? contract world invocation fuel = some result) :
    world.code? invocation.target = some contract.code := by
  obtain ⟨installed, _⟩ := phase?_eq_some ran
  exact TopLevelExecution.initialWorld_code? installed

theorem phase?_completed_balance?
    {contract : CheckedCoreContract} {world : WorldState} {invocation : TopLevelInvocation}
    {fuel : Nat} {result : TopLevelTerminalResult world invocation.target}
    (ran : phase? contract world invocation fuel = some (.completed result)) (observed : Address) :
    result.finalWorld.balance? observed = world.balance? observed := by
  obtain ⟨installed, completed⟩ := phase?_eq_some ran
  exact TopLevelExecution.run_completed_balance? contract invocation installed fuel completed observed

theorem childStep_balance?
    {registry : CheckedContractRegistry} {parent : Address} {request : Request}
    {world : WorldState} {fuel : Nat} {child : ChildResult}
    (stepped : childStep registry parent request world fuel = some child) (observed : Address) :
    child.world.balance? observed = world.balance? observed := by
  unfold childStep at stepped
  split at stepped
  · cases stepped
    rfl
  · split at stepped
    · cases stepped
      rfl
    · split at stepped
      · cases stepped
      · rename_i completed
        split at stepped
        · cases stepped
          exact TopLevelExecution.run_completed_balance? _ _ _ _ completed observed
        · cases stepped
          rfl
        · cases stepped
          rfl

/-- Every account's balance after a completed transaction is the one before. -/
theorem run_balance?
    {registry : CheckedContractRegistry} {contract : CallResumeParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
    {requested : Option Request} {childResult : Option ChildResult}
    (completed : run registry contract world parent caller input fuel =
      .completed outcome finalWorld requested childResult)
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
      · cases completed
      · rename_i stepped
        unfold resumeStep at completed
        split at completed
        · split at completed
          · cases completed
          · cases completed
          · rename_i resumed ranResume
            split at completed
            · cases completed
              rw [withCodeAt_balance?, phase?_completed_balance? ranResume, withCodeAt_balance?,
                childStep_balance? stepped, phase?_completed_balance? ran]
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

/-- The parent's code after a completed transaction is the call phase's, as
before it. -/
theorem run_code?
    {registry : CheckedContractRegistry} {contract : CallResumeParent} {world : WorldState}
    {parent caller : Address} {input : HostStorageDriver.InputData} {fuel : Nat}
    {outcome : FrameOutcome Core.Word} {finalWorld : WorldState}
    {requested : Option Request} {childResult : Option ChildResult}
    (completed : run registry contract world parent caller input fuel =
      .completed outcome finalWorld requested childResult) :
    finalWorld.code? parent = world.code? parent := by
  unfold run at completed
  split at completed
  · cases completed
  · cases completed
  · rename_i called ran
    have installedCall : world.code? parent = some contract.call.code := phase?_code? ran
    split at completed
    · cases completed
      rfl
    · cases completed
      rfl
    · split at completed
      · cases completed
      · unfold resumeStep at completed
        split at completed
        · split at completed
          · cases completed
          · cases completed
          · rename_i resumed ranResume
            split at completed
            · cases completed
              rw [installedCall]
              exact withCodeAt_code? _ _ _ resumed.committedDelta.finalAccount_present
            · cases completed
              rfl
            · cases completed
              rfl
        · cases completed

end CallResumeExecution

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.CallChainExecution
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

namespace CallChainExecution

open CallResumeExecution (Request ChildResult childStep resumeInputBytes phase? withCodeAt
  parentInvocation)

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

end CallChainExecution

end Solcore.ContractRuntime
end

section
-- leanmerge: from Solcore.ContractRuntime.CallChoiceExecution
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

namespace CallChoiceExecution

open CallResumeExecution (Request ChildResult childStep resumeInputBytes phase? withCodeAt
  parentInvocation wordAt)

open CallChainExecution (Stage Call)

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

end CallChoiceExecution

end Solcore.ContractRuntime
end
