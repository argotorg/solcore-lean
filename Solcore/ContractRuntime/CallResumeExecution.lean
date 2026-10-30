import Solcore.ContractRuntime.TopLevelExecution
import Solcore.ContractRuntime.CheckedContractRegistry
import Solcore.ContractRuntime.CoreContractEntryProfileProperties
import Solcore.ContractRuntime.WorldStateBalanceProperties
import Solcore.ContractRuntime.AddressWordBridge

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
