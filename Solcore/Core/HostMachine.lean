import Solcore.Core.Host
import Solcore.Core.Machine

/-! First-order host requests and resumable Core-machine suspensions. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostRequest where
  | storageRead (slot : Word)
  deriving Repr, BEq, DecidableEq

namespace HostRequest

/-- The host-language response required by a particular request. -/
def Response : HostRequest → Type
  | .storageRead _ => Word

/-- Core type injected when a request is resumed. -/
def responseType : HostRequest → Ty
  | .storageRead _ => .word

/-- Convert an indexed host response back into a Core runtime value. -/
def responseValue
    (request : HostRequest)
    (response : request.Response) : Value :=
  match request with
  | .storageRead _ => .word response

@[simp] theorem responseType_storageRead (slot : Word) :
    responseType (.storageRead slot) = .word :=
  rfl

@[simp] theorem responseValue_storageRead (slot response : Word) :
    responseValue (.storageRead slot) response = .word response :=
  rfl

@[simp] theorem responseValue_type
    (request : HostRequest)
    (response : request.Response) :
    (request.responseValue response).type = request.responseType := by
  cases request
  rfl

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

end HostSuspension

end Solcore.Core
