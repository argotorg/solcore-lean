import Solcore.Core.Host
import Solcore.Core.Machine

/-! First-order host requests and resumable Core-machine suspensions. -/

set_option autoImplicit false

namespace Solcore.Core

inductive HostRequest where
  | storageRead (slot : Word)
  | storageWrite (slot value : Word)
  | storageAddress
  | codeAddress
  | callValue
  | callerAddress
  | inputDataByte? (offset : Word)
  | inputDataSize
  | inputDataWordBE? (offset : Word)
  deriving Repr, BEq, DecidableEq

namespace HostRequest

/-- The host-language response required by a particular request. -/
def Response : HostRequest → Type
  | .storageRead _ => Word
  | .storageWrite _ _ => Unit
  | .storageAddress => Word
  | .codeAddress => Word
  | .callValue => Word
  | .callerAddress => Word
  | .inputDataByte? _ => Option Word
  | .inputDataSize => Word
  | .inputDataWordBE? _ => Option Word

/-- Core type injected when a request is resumed. -/
def responseType : HostRequest → Ty
  | .storageRead _ => .word
  | .storageWrite _ _ => .unit
  | .storageAddress => .word
  | .codeAddress => .word
  | .callValue => .word
  | .callerAddress => .word
  | .inputDataByte? _ => .sum .unit .word
  | .inputDataSize => .word
  | .inputDataWordBE? _ => .sum .unit .word

/-- Convert an indexed host response back into a Core runtime value. -/
def responseValue
    (request : HostRequest)
    (response : request.Response) : Value :=
  match request with
  | .storageRead _ => .word response
  | .storageWrite _ _ => .unit
  | .storageAddress => .word response
  | .codeAddress => .word response
  | .callValue => .word response
  | .callerAddress => .word response
  | .inputDataByte? _ =>
      match response with
      | none => .inLeft .word .unit
      | some byte => .inRight .unit (.word byte)
  | .inputDataSize => .word response
  | .inputDataWordBE? _ =>
      match response with
      | none => .inLeft .word .unit
      | some word => .inRight .unit (.word word)

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

@[simp] theorem responseType_storageAddress :
    responseType .storageAddress = .word :=
  rfl

@[simp] theorem responseValue_storageAddress (response : Word) :
    responseValue .storageAddress response = .word response :=
  rfl

@[simp] theorem responseType_codeAddress :
    responseType .codeAddress = .word :=
  rfl

@[simp] theorem responseValue_codeAddress (response : Word) :
    responseValue .codeAddress response = .word response :=
  rfl

@[simp] theorem responseType_callValue :
    responseType .callValue = .word :=
  rfl

@[simp] theorem responseValue_callValue (response : Word) :
    responseValue .callValue response = .word response :=
  rfl

@[simp] theorem responseType_callerAddress :
    responseType .callerAddress = .word :=
  rfl

@[simp] theorem responseValue_callerAddress (response : Word) :
    responseValue .callerAddress response = .word response :=
  rfl

@[simp] theorem responseType_inputDataByte? (offset : Word) :
    responseType (.inputDataByte? offset) = .sum .unit .word :=
  rfl

@[simp] theorem responseValue_inputDataByte?_none (offset : Word) :
    responseValue (.inputDataByte? offset) none = .inLeft .word .unit :=
  rfl

@[simp] theorem responseValue_inputDataByte?_some (offset byte : Word) :
    responseValue (.inputDataByte? offset) (some byte) =
      .inRight .unit (.word byte) :=
  rfl

@[simp] theorem responseType_inputDataSize :
    responseType .inputDataSize = .word :=
  rfl

@[simp] theorem responseValue_inputDataSize (response : Word) :
    responseValue .inputDataSize response = .word response :=
  rfl

@[simp] theorem responseType_inputDataWordBE? (offset : Word) :
    responseType (.inputDataWordBE? offset) = .sum .unit .word :=
  rfl

@[simp] theorem responseValue_inputDataWordBE?_none (offset : Word) :
    responseValue (.inputDataWordBE? offset) none = .inLeft .word .unit :=
  rfl

@[simp] theorem responseValue_inputDataWordBE?_some
    (offset word : Word) :
    responseValue (.inputDataWordBE? offset) (some word) =
      .inRight .unit (.word word) :=
  rfl

@[simp] theorem responseValue_type
    (request : HostRequest)
    (response : request.Response) :
    (request.responseValue response).type = request.responseType := by
  cases request <;> try rfl
  all_goals cases response <;> rfl

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

@[simp] theorem resume_storageAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .storageAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_codeAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .codeAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_callValue
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .callValue continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_callerAddress
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .callerAddress continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataByte?_none
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataByte? offset) continuation store).resume none =
      ⟨.ret (.inLeft .word .unit), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataByte?_some
    (offset byte : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataByte? offset) continuation store).resume
        (some byte) =
      ⟨.ret (.inRight .unit (.word byte)), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataSize
    (response : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk .inputDataSize continuation store).resume response =
      ⟨.ret (.word response), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataWordBE?_none
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
        none =
      ⟨.ret (.inLeft .word .unit), continuation, store⟩ :=
  rfl

@[simp] theorem resume_inputDataWordBE?_some
    (offset word : Word)
    (continuation : List Frame)
    (store : Store) :
    (HostSuspension.mk (.inputDataWordBE? offset) continuation store).resume
        (some word) =
      ⟨.ret (.inRight .unit (.word word)), continuation, store⟩ :=
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
      match function with
      | .storageRead =>
          match argument with
          | .word slot =>
              .suspended {
                request := .storageRead slot
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .storageRead actual)
      | .storageWrite =>
          match argument with
          | .pair (.word slot) (.word value) =>
              .suspended {
                request := .storageWrite slot value
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .storageWrite actual)
      | .storageAddress =>
          match argument with
          | .unit =>
              .suspended {
                request := .storageAddress
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .storageAddress actual)
      | .codeAddress =>
          match argument with
          | .unit =>
              .suspended {
                request := .codeAddress
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .codeAddress actual)
      | .callValue =>
          match argument with
          | .unit =>
              .suspended {
                request := .callValue
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .callValue actual)
      | .callerAddress =>
          match argument with
          | .unit =>
              .suspended {
                request := .callerAddress
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .callerAddress actual)
      | .inputDataByte? =>
          match argument with
          | .word offset =>
              .suspended {
                request := .inputDataByte? offset
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .inputDataByte? actual)
      | .inputDataSize =>
          match argument with
          | .unit =>
              .suspended {
                request := .inputDataSize
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .inputDataSize actual)
      | .inputDataWordBE? =>
          match argument with
          | .word offset =>
              .suspended {
                request := .inputDataWordBE? offset
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .inputDataWordBE? actual)
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
  cases actual with
  | pair left right =>
      cases left <;> cases right <;> simp_all [hostAdvance]
  | unit | bool | word | hostFunction | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_storageAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .storageAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .storageAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_storageAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .storageAddress :: continuation, store⟩ =
      .suspended ⟨.storageAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_storageAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .storageAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .storageAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_codeAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .codeAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .codeAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_codeAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .codeAddress :: continuation, store⟩ =
      .suspended ⟨.codeAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_codeAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .codeAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .codeAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_callValue
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callValue),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callValue :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callValue
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .callValue :: continuation, store⟩ =
      .suspended ⟨.callValue, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callValue_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .callValue :: continuation, store⟩ =
      .fault (.invalidHostArgument .callValue actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_callerAddress
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .callerAddress),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .callerAddress :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_callerAddress
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .callerAddress :: continuation, store⟩ =
      .suspended ⟨.callerAddress, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_callerAddress_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .callerAddress :: continuation, store⟩ =
      .fault (.invalidHostArgument .callerAddress actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_inputDataByte?
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataByte?),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataByte? :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataByte?
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word offset), .hostApply .inputDataByte? :: continuation, store⟩ =
      .suspended ⟨.inputDataByte? offset, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataByte?_argument
    (actual : Value)
    (notWord : ∀ offset, actual ≠ .word offset)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataByte? :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataByte? actual) := by
  cases actual <;> simp_all [hostAdvance]

@[simp] theorem hostAdvance_begin_inputDataSize
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataSize),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataSize :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataSize
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret .unit, .hostApply .inputDataSize :: continuation, store⟩ =
      .suspended ⟨.inputDataSize, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataSize_argument
    (actual : Value)
    (notUnit : actual ≠ .unit)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataSize :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataSize actual) := by
  cases actual with
  | unit => exact (notUnit rfl).elim
  | bool | word | hostFunction | pair | closure | inLeft | inRight | cellRef |
      constructed =>
      rfl

@[simp] theorem hostAdvance_begin_inputDataWordBE?
    (argument : Expr)
    (environment : Environment)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.hostFunction .inputDataWordBE?),
          .applyArgument argument environment :: continuation, store⟩ =
      .next
        ⟨.eval argument environment,
          .hostApply .inputDataWordBE? :: continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_suspend_inputDataWordBE?
    (offset : Word)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret (.word offset),
          .hostApply .inputDataWordBE? :: continuation, store⟩ =
      .suspended ⟨.inputDataWordBE? offset, continuation, store⟩ :=
  rfl

@[simp] theorem hostAdvance_invalid_inputDataWordBE?_argument
    (actual : Value)
    (notWord : ∀ offset, actual ≠ .word offset)
    (continuation : List Frame)
    (store : Store) :
    hostAdvance
        ⟨.ret actual, .hostApply .inputDataWordBE? :: continuation, store⟩ =
      .fault (.invalidHostArgument .inputDataWordBE? actual) := by
  cases actual <;> simp_all [hostAdvance]

end Solcore.Core
