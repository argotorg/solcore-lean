import Solcore.Core.Host
import Solcore.Core.Machine

/-! First-order host requests and resumable Core-machine suspensions. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  deriving Repr, BEq, DecidableEq

namespace HostRequest

/-- The host-language response required by a particular request. -/
def Response : HostRequest → Type
  | .storageRead _ => Word
  | .storageWrite _ _ => Unit

/-- Core type injected when a request is resumed. -/
def responseType : HostRequest → Ty
  | .storageRead _ => .word
  | .storageWrite _ _ => .unit

/-- Convert an indexed host response back into a Core runtime value. -/
def responseValue
    (request : HostRequest)
    (response : request.Response) : Value :=
  match request with
  | .storageRead _ => .word response
  | .storageWrite _ _ => .unit

@[simp] theorem responseType_storageRead (slot : Word) :
    responseType (.storageRead slot) = .word :=
  rfl

@[simp] theorem responseValue_storageRead (slot response : Word) :
    responseValue (.storageRead slot) response = .word response :=
  rfl

@[simp] theorem responseType_storageWrite (slot value : Word) :
    responseType (.storageWrite slot value) = .unit :=
  rfl

@[simp] theorem responseValue_storageWrite
    (slot value : Word)
    (response : Unit) :
    responseValue (.storageWrite slot value) response = .unit :=
  rfl

@[simp] theorem responseValue_type
    (request : HostRequest)
    (response : request.Response) :
    (request.responseValue response).type = request.responseType := by
  cases request <;> rfl

end HostRequest

/-- A request together with the exact CEK continuation and Core-local store. -/
structure HostSuspension where
  request : HostRequest
  continuation : List Frame
  store : Store
  deriving Repr, BEq, DecidableEq

namespace HostSuspension

/-- Resume exactly where the request was emitted using a typed response. -/
def resume
    (suspension : HostSuspension)
    (response : suspension.request.Response) : State := {
  control := .ret (suspension.request.responseValue response)
  continuation := suspension.continuation
  store := suspension.store
}

@[simp] theorem resume_control
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).control =
      .ret (suspension.request.responseValue response) :=
  rfl

@[simp] theorem resume_continuation
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).continuation = suspension.continuation :=
  rfl

@[simp] theorem resume_store
    (suspension : HostSuspension)
    (response : suspension.request.Response) :
    (suspension.resume response).store = suspension.store :=
  rfl

@[simp] theorem resume_storageRead
    (slot response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.storageRead slot) continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_storageWrite
    (slot value : Word)
    (response : Unit)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.storageWrite slot value) continuation store).resume
        response =
      ⟨.ret .unit, continuation, store⟩ :=
  rfl

end HostSuspension

/-- One executable step at the Core/host boundary. -/
inductive HostAdvanceResult where
  | next (state : State)
  | done (value : Value)
  | fault (error : MachineFault)
  | suspended (suspension : HostSuspension)
  deriving Repr, BEq, DecidableEq

namespace HostAdvanceResult

def ofAdvance : AdvanceResult → HostAdvanceResult
  | .next state => .next state
  | .done value => .done value
  | .fault error => .fault error

@[simp] theorem ofAdvance_next (state : State) :
    ofAdvance (.next state) = .next state :=
  rfl

@[simp] theorem ofAdvance_done (value : Value) :
    ofAdvance (.done value) = .done value :=
  rfl

@[simp] theorem ofAdvance_fault (error : MachineFault) :
    ofAdvance (.fault error) = .fault error :=
  rfl

end HostAdvanceResult

/--
Advance ordinary Core states normally, but turn application of a supplied host
function into argument evaluation followed by a first-order suspension.
-/
def hostAdvance (state : State) : HostAdvanceResult :=
  match state.control, state.continuation with
  | .ret (.hostFunction function),
      .applyArgument argument environment :: continuation =>
      .next {
        control := .eval argument environment
        continuation := .hostApply function :: continuation
        store := state.store
      }
  | .ret argument, .hostApply function :: continuation =>
      match function, argument with
      | .storageRead, .word slot =>
          .suspended {
            request := .storageRead slot
            continuation
            store := state.store
          }
      | .storageWrite, .pair (.word slot) (.word value) =>
          .suspended {
            request := .storageWrite slot value
            continuation
            store := state.store
          }
      | function, actual => .fault (.invalidHostArgument function actual)
  | _, _ => .ofAdvance (advance state)

@[simp] theorem hostAdvance_begin_storageRead
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageRead),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageRead :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageRead
    (slot : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word slot), .hostApply .storageRead :: continuation, store⟩ =
      .suspended ⟨.storageRead slot, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageRead_argument
    (actual : Value)
    (notWord : ∀ slot, actual ≠ .word slot)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageRead :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageRead actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_storageWrite
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageWrite),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageWrite :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageWrite
    (slot value : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.pair (.word slot) (.word value)),
          .hostApply .storageWrite :: continuation, store⟩ =
      .suspended ⟨.storageWrite slot value, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageWrite_argument
    (actual : Value)
    (notWordPair :
      ∀ slot value,
        actual ≠ .pair (.word slot) (.word value))
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageWrite :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageWrite actual) := by
  cases actual <;> simp_all [hostAdvance]

end Solcore.Core
