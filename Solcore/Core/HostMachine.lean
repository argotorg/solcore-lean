import Solcore.Core.Host
import Solcore.Core.Machine

/-!
# Host requests

A program that calls a `HostFunction` suspends. `HostRequest` is the first-order request,
`HostSuspension` the state to resume with `HostSuspension.resume`, and `ContractCallWordResult` the
answer to a call. `hostAdvance` is the step and `HostAdvanceResult` its result, and `HostTransition`
and `HostRequestEmission` are the same step as relations.
-/

/-! First-order host requests and resumable Core-machine suspensions. -/

set_option autoImplicit false

namespace Solcore.Core

/-- Typed, lossless result delivered to Core after one contract-word call. -/
inductive ContractCallWordResult where
  | returned (data : Word)
  | reverted (data : Word)
  | trapped (reason : Word)
  | failed (reason : Word)
  deriving Repr, BEq, DecidableEq

namespace ContractCallWordResult

/-- The fixed Core sum used by the internal contract-word call capability. -/
def resultType : Ty :=
  .sum .word (.sum .word (.sum .word .word))

/-- Inject every call disposition into a distinct branch of the fixed sum. -/
def value : ContractCallWordResult → Value
  | .returned data =>
      .inLeft (.sum .word (.sum .word .word)) (.word data)
  | .reverted data =>
      .inRight .word (.inLeft (.sum .word .word) (.word data))
  | .trapped reason =>
      .inRight .word (.inRight .word (.inLeft .word (.word reason)))
  | .failed reason =>
      .inRight .word (.inRight .word (.inRight .word (.word reason)))

end ContractCallWordResult

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
  | currentAddress
  | callContractWord (target input : Word)
  | callContractWordWithValue (target value input : Word)
  | createContractWord (templateId value input : Word)
  | emitLogWord (topic payload : Word)
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
  | .currentAddress => Word
  | .callContractWord _ _ => ContractCallWordResult
  | .callContractWordWithValue _ _ _ => ContractCallWordResult
  | .createContractWord _ _ _ => ContractCallWordResult
  | .emitLogWord _ _ => Unit

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
  | .currentAddress => .word
  | .callContractWord _ _ => ContractCallWordResult.resultType
  | .callContractWordWithValue _ _ _ => ContractCallWordResult.resultType
  | .createContractWord _ _ _ => ContractCallWordResult.resultType
  | .emitLogWord _ _ => .unit

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
  | .currentAddress => .word response
  | .callContractWord _ _ => response.value
  | .callContractWordWithValue _ _ _ => response.value
  | .createContractWord _ _ _ => response.value
  | .emitLogWord _ _ => .unit

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
      | .currentAddress =>
          match argument with
          | .unit =>
              .suspended {
                request := .currentAddress
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .currentAddress actual)
      | .callContractWord =>
          match argument with
          | .pair (.word target) (.word input) =>
              .suspended {
                request := .callContractWord target input
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .callContractWord actual)
      | .callContractWordWithValue =>
          match argument with
          | .pair (.word target) (.pair (.word value) (.word input)) =>
              .suspended {
                request := .callContractWordWithValue target value input
                continuation
                store := state.store
              }
          | actual =>
              .fault (.invalidHostArgument .callContractWordWithValue actual)
      | .createContractWord =>
          match argument with
          | .pair (.word templateId) (.pair (.word value) (.word input)) =>
              .suspended {
                request := .createContractWord templateId value input
                continuation
                store := state.store
              }
          | actual =>
              .fault (.invalidHostArgument .createContractWord actual)
      | .emitLogWord =>
          match argument with
          | .pair (.word topic) (.word payload) =>
              .suspended {
                request := .emitLogWord topic payload
                continuation
                store := state.store
              }
          | actual => .fault (.invalidHostArgument .emitLogWord actual)
  | _, _ => .ofAdvance (advance state)

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.HostMachineProperties`
-/

/-! Declarative one-step relations for the executable Core/host boundary. -/

set_option autoImplicit false

namespace Solcore.Core

/--
An ordinary step of the host-aware machine. Core transitions are preserved,
while applying a host function first evaluates its Core argument.
-/
inductive HostTransition : State → State → Prop where
  | core
      {state next : State}
      (step : Transition state next) :
      HostTransition state next
  | beginApplication
      {function : HostFunction}
      {argument : Expr}
      {environment : Environment}
      {continuation : List Frame}
      {store : Store} :
      HostTransition
        ⟨.ret (.hostFunction function),
          .applyArgument argument environment :: continuation, store⟩
        ⟨.eval argument environment,
          .hostApply function :: continuation, store⟩

/-- A state emits a particular first-order host request and suspension. -/
inductive HostRequestEmission : State → HostSuspension → Prop where
  | storageRead
      {slot : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word slot), .hostApply .storageRead :: continuation, store⟩
        ⟨.storageRead slot, continuation, store⟩
  | storageWrite
      {slot value : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.pair (.word slot) (.word value)),
          .hostApply .storageWrite :: continuation, store⟩
        ⟨.storageWrite slot value, continuation, store⟩
  | storageAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .storageAddress :: continuation, store⟩
        ⟨.storageAddress, continuation, store⟩
  | codeAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .codeAddress :: continuation, store⟩
        ⟨.codeAddress, continuation, store⟩
  | callValue
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .callValue :: continuation, store⟩
        ⟨.callValue, continuation, store⟩
  | callerAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .callerAddress :: continuation, store⟩
        ⟨.callerAddress, continuation, store⟩
  | inputDataByte?
      {offset : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word offset), .hostApply .inputDataByte? :: continuation, store⟩
        ⟨.inputDataByte? offset, continuation, store⟩
  | inputDataSize
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .inputDataSize :: continuation, store⟩
        ⟨.inputDataSize, continuation, store⟩
  | inputDataWordBE?
      {offset : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.word offset),
          .hostApply .inputDataWordBE? :: continuation, store⟩
        ⟨.inputDataWordBE? offset, continuation, store⟩
  | currentAddress
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret .unit, .hostApply .currentAddress :: continuation, store⟩
        ⟨.currentAddress, continuation, store⟩
  | callContractWord
      {target input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.pair (.word target) (.word input)),
          .hostApply .callContractWord :: continuation, store⟩
        ⟨.callContractWord target input, continuation, store⟩
  | callContractWordWithValue
      {target value input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret
            (.pair (.word target) (.pair (.word value) (.word input))),
          .hostApply .callContractWordWithValue :: continuation, store⟩
        ⟨.callContractWordWithValue target value input,
          continuation, store⟩
  | createContractWord
      {templateId value input : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret
            (.pair (.word templateId) (.pair (.word value) (.word input))),
          .hostApply .createContractWord :: continuation, store⟩
        ⟨.createContractWord templateId value input,
          continuation, store⟩
  | emitLogWord
      {topic payload : Word}
      {continuation : List Frame}
      {store : Store} :
      HostRequestEmission
        ⟨.ret (.pair (.word topic) (.word payload)),
          .hostApply .emitLogWord :: continuation, store⟩
        ⟨.emitLogWord topic payload, continuation, store⟩

end Solcore.Core
