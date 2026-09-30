import Solcore.Core.LanguageResult
import Solcore.ContractRuntime.HostDriver
import Solcore.ContractRuntime.TopLevelExecution

/-! Decode the ordinary Core language-result sum at the contract boundary.
The success callback keeps the existing entry codec. Language failures become
frame traps; malformed carriers, machine faults and fuel checkpoints stay
distinct. This adapter does not interpret source syntax or add machine states. -/

set_option autoImplicit false

namespace Solcore.ContractRuntime.CoreLanguageResult

universe u v w

/-- Decode only the outer language envelope. Typed callers certify its type
annotations and the success payload; the existing success codec is unchanged. -/
def decodeDone? {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (value : Core.Value) (store : Core.Store) :
    Option (FrameOutcome Core.Word) :=
  (Core.LanguageResult.decode? value).map fun
    | .succeeded payload => success context payload store
    | .failed reason => .trapped reason

/-- Preserve unfinished execution and raw internal faults without turning
either into a terminal language outcome. -/
inductive Outcome where
  | completed (carrier : Core.Value) (store : Core.Store)
      (frame : FrameOutcome Core.Word)
  | invalidCarrier (carrier : Core.Value) (store : Core.Store)
  | outOfFuel (state : Core.State)
  | fault (error : Core.MachineFault) (state : Core.State)
  | unsupported (suspension : Core.HostSuspension) (remainingFuel : Nat)

structure Result (Context : Type u) where
  context : Context
  outcome : Outcome

def decode {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context) : Result Context :=
  ⟨result.context, match result.outcome with
    | .done value store => match decodeDone? success result.context value store with
      | some frame => .completed value store frame
      | none => .invalidCarrier value store
    | .outOfFuel state => .outOfFuel state
    | .fault error state => .fault error state
    | .unsupported suspension remaining => .unsupported suspension remaining⟩

/-- The existing host driver performs all requests and fuel accounting. -/
def run {Context : Type u} (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (fuel : Nat) (state : Core.State) : Result Context :=
  decode success (HostDriver.run handler context fuel state)

@[simp] theorem decodeDone?_success {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (value : Core.Value) (store : Core.Store) :
    decodeDone? success context (.inRight .word value) store =
      some (success context value store) := rfl

@[simp] theorem decodeDone?_failure {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (type : Core.Ty) (reason : Core.Word) (store : Core.Store) :
    decodeDone? success context (.inLeft type (.word reason)) store =
      some (.trapped reason) := rfl

/-- The success payload retains the host-runtime typing of the outer sum. -/
theorem decode?_host_typed
    {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {type : Core.Ty}
    (typed : Core.HostRuntimeValueHasType world value
      (Core.LanguageResult.resultType type) definitions) :
    ∃ outcome, Core.LanguageResult.decode? value = some outcome ∧
      match outcome with
      | .succeeded payload => Core.HostRuntimeValueHasType world payload type definitions
      | .failed _ => True := by
  cases typed with
  | inLeft payload =>
      cases payload with
      | word => exact ⟨_, rfl, trivial⟩
  | inRight payload => exact ⟨_, rfl, payload⟩

/-- Every host-typed language result has an envelope the adapter accepts. -/
theorem decodeDone?_ne_none_of_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (store : Core.Store)
    {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {type : Core.Ty}
    (typed : Core.HostRuntimeValueHasType world value
      (Core.LanguageResult.resultType type) definitions) :
    decodeDone? success context value store ≠ none := by
  cases typed with
  | inLeft payload =>
      cases payload
      simp [decodeDone?]
  | inRight payload => simp [decodeDone?]

theorem decode_ne_invalidCarrier_of_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : result.outcome.HasType (Core.LanguageResult.resultType type) definitions)
    (value : Core.Value) (store : Core.Store) :
    (decode success result).outcome ≠ .invalidCarrier value store := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done carrier localStore =>
          obtain ⟨world, _, carrierTyped⟩ := typed
          have accepted := decodeDone?_ne_none_of_hasType success context localStore
            carrierTyped
          cases decoded : decodeDone? success context carrier localStore with
          | none => exact False.elim (accepted decoded)
          | some frame => simp [decode, decoded]
      | outOfFuel | fault | unsupported => simp [decode]

/-- The adapter retains the underlying host typing and rejects both malformed
envelopes and internal faults at typed entry points. The caller owns its codec. -/
def Outcome.HasType (outcome : Outcome) (type : Core.Ty)
    (definitions : Core.DataEnvironment := []) : Prop :=
  match outcome with
  | .completed carrier store _ =>
      ∃ world, Core.HostStoreHasTypes world store definitions ∧
        Core.HostRuntimeValueHasType world carrier (Core.LanguageResult.resultType type) definitions
  | .outOfFuel state => Core.HostStateHasType state (Core.LanguageResult.resultType type) definitions
  | .unsupported suspension _ =>
      Core.HostSuspensionHasType suspension (Core.LanguageResult.resultType type) definitions
  | .invalidCarrier _ _ | .fault _ _ => False

theorem decode_hasType {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (result : HostDriverResult Context)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : result.outcome.HasType (Core.LanguageResult.resultType type) definitions) :
    (decode success result).outcome.HasType type definitions := by
  cases result with
  | mk context outcome =>
      cases outcome with
      | done carrier store =>
          obtain ⟨world, storeTyped, carrierTyped⟩ := typed
          have accepted := decodeDone?_ne_none_of_hasType success context store carrierTyped
          cases decoded : decodeDone? success context carrier store with
          | none => exact False.elim (accepted decoded)
          | some frame =>
              simp only [decode, decoded, Outcome.HasType]
              exact ⟨world, storeTyped, carrierTyped⟩
      | outOfFuel | fault | unsupported => exact typed

theorem run_hasType {Context : Type u}
    (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (fuel : Nat) (state : Core.State)
    {definitions : Core.DataEnvironment} {type : Core.Ty}
    (typed : Core.HostStateHasType state (Core.LanguageResult.resultType type) definitions) :
    (run handler success context fuel state).outcome.HasType type definitions :=
  decode_hasType success _ (HostDriver.run_hasType handler context fuel state typed)

@[simp] theorem decode_outOfFuel {Context : Type u}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (state : Core.State) :
    decode success ⟨context, .outOfFuel state⟩ =
      ⟨context, .outOfFuel state⟩ := rfl

/-- The exact host-run completion is decoded after the unchanged driver step. -/
theorem run_of_host_done {Context : Type u}
    (handler : HostHandler Context)
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) {fuel : Nat} {state : Core.State}
    {value : Core.Value} {store : Core.Store}
    (done : Core.hostRun fuel state = .done value store) :
    run handler success context fuel state = decode success ⟨context, .done value store⟩ := by
  unfold run
  rw [HostDriver.run, done]

def Result.toFrame? {Context : Type u} {RollbackState : Type v} {TraceState : Type w}
    (result : Result Context)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    Option (FrameContinuationContext RollbackState TraceState Core.Word) :=
  match result.outcome with
  | .completed _ _ frame =>
      some (FrameContinuationContext.fromCheckpointedWorkingPair (values result.context) frame)
  | _ => none

@[simp] theorem toFrame?_outOfFuel {Context : Type u}
    {RollbackState : Type v} {TraceState : Type w}
    (context : Context) (state : Core.State)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    (Result.mk context (.outOfFuel state)).toFrame? values = none := rfl

theorem failure_resolves_trapped {Context : Type u}
    {RollbackState : Type v} {TraceState : Type w}
    (success : Context → Core.Value → Core.Store → FrameOutcome Core.Word)
    (context : Context) (type : Core.Ty) (reason : Core.Word) (store : Core.Store)
    (values : Context → FrameCheckpointedWorkingPair RollbackState TraceState) :
    ((decode success ⟨context, .done (.inLeft type (.word reason)) store⟩).toFrame? values).map
        FrameContinuationContext.resolve = some (.trapped reason) := rfl

/-- Reuse the established root finalizer only for decoded completed values.
The caller supplies the same working-world and checkpoint evidence as before. -/
def Result.finalize? {initialWorld : WorldState}
    (result : Result TransactionHostStorageDriver.Context)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      result.context.context.values.working.1 invocation.target)
    (checkpoint : result.context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    Option (TopLevelTerminalResult initialWorld invocation.target) :=
  match result.outcome with
  | .completed carrier store frame => some (TopLevelExecution.finalize invocation
      account present result.context carrier store frame delta checkpoint)
  | _ => none

/-- A language failure follows the existing trap rollback policy, including
rollback-scoped observations; speculative state is still retained for inspection. -/
theorem failure_finalizes_rollback {initialWorld : WorldState}
    (success : TransactionHostStorageDriver.Context → Core.Value → Core.Store →
      FrameOutcome Core.Word)
    (context : TransactionHostStorageDriver.Context)
    (type : Core.Ty) (reason : Core.Word) (store : Core.Store)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      context.context.values.working.1 invocation.target)
    (checkpoint : context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    let finalized := (decode success
      ⟨context, .done (.inLeft type (.word reason)) store⟩).finalize?
        invocation account present delta checkpoint
    finalized.map (·.finalWorld) = some initialWorld ∧
      finalized.map (·.committedJournal) = some TransactionJournal.empty ∧
      finalized.map (·.workingJournal) = some context.workingJournal := by
  dsimp [decode, decodeDone?, Core.LanguageResult.decode?, Result.finalize?,
    TopLevelExecution.finalize]
  exact ⟨rfl, congrArg some checkpoint, rfl⟩

@[simp] theorem finalize?_outOfFuel {initialWorld : WorldState}
    (context : TransactionHostStorageDriver.Context) (state : Core.State)
    (invocation : TopLevelInvocation) (account : Account)
    (present : initialWorld.account? invocation.target = some account)
    (delta : TopLevelStorageDelta initialWorld
      context.context.values.working.1 invocation.target)
    (checkpoint : context.context.values.checkpoint.effects.rollback =
      TransactionJournal.empty) :
    (Result.mk context (.outOfFuel state)).finalize?
      invocation account present delta checkpoint = none := rfl

end Solcore.ContractRuntime.CoreLanguageResult
