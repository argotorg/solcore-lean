import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
import Solcore.Frontend.RustHull.RuntimeLifecycleSemantics
import Solcore.Frontend.RustHull.CreationSemantics

/-! Message call modes share caller transport and account checkpoints. The
mode controls the handler, caller observation and stipend checks; account
dispatch controls execution address and balance transfer separately. Account
destruction shares the same frame state and transaction world, and so do
creation attempts refused before init code runs. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallModeSemantics
open Core

abbrev State := RuntimeCallEffectsSemantics.State
abbrev shared := RuntimeCallEffectsSemantics.shared
abbrev transport := RuntimeCallEffectsSemantics.transport
abbrev withTransport := RuntimeCallEffectsSemantics.withTransport
abbrev invalid := RuntimeCallEffectsSemantics.invalid

inductive Operation where
  | ordinary | staticCall | callCode | delegateCall
  deriving DecidableEq, BEq, Repr

def Operation.name : Operation → String
  | .ordinary => "call" | .staticCall => "staticcall"
  | .callCode => "callcode" | .delegateCall => "delegatecall"

def Operation.mode : Operation → AccountCallSemantics.Mode
  | .ordinary | .staticCall => .ordinary
  | .callCode => .callCode | .delegateCall => .delegateCall

def Operation.hasStipend : Operation → Bool
  | .ordinary | .callCode => true
  | .staticCall | .delegateCall => false

def observations (state : State) : EnvironmentSemantics.State :=
  state.runtime.runtime.runtime.runtime.environment

def arguments (operation : Operation) (state : State)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) : CallTransportSemantics.Arguments :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {caller := if operation = .delegateCall then (observations state).direct .caller else runtime.storage.address
   depth := state.callDepth
   isStatic := if operation = .staticCall then true else runtime.storage.isStatic
   gas := if operation.hasStipend ∧ value ≠ Word.zero then gas.add (Word.ofNatModulo 2300) else gas
   target := target, value := value, inputOffset := inputOffset, inputLength := inputLength
   outputOffset := outputOffset, outputLength := outputLength}

/-- CALLCODE admits nonzero value in a static frame, but its child still
inherits the static flag. Only ordinary CALL rejects that value at this stage. -/
inductive Call (children : State → AccountCallSemantics.Children) (operation : Operation)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | staticValue (state : State)
      (ordinary : operation = .ordinary)
      (isStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = true)
      (nonzero : value ≠ Word.zero) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (invalid state).1 (invalid state).2
  | gasOverflow (state : State)
      (stipend : operation.hasStipend = true)
      (permitted : operation ≠ .ordinary ∨ state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (nonzero : value ≠ Word.zero)
      (overflow : gas > Word.ofNatModulo (wordModulus - 2301)) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (.fault (.language (Word.ofNatModulo 13))) state
  | invoked {state : State} {next : CallTransportSemantics.State} {nextShared : AccountCallSemantics.Shared}
      {result : Semantics.Result Semantics.Value}
      (permitted : operation ≠ .ordinary ∨ value = Word.zero ∨
        state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (stipend : operation.hasStipend = true → value ≠ Word.zero →
        ¬gas > Word.ofNatModulo (wordModulus - 2301))
      (executed : CallTransportSemantics.Execute
        (AccountCallSemantics.Dispatch (children state) operation.mode
          state.runtime.runtime.runtime.runtime.runtime.storage.address)
        true (arguments operation state gas target value inputOffset inputLength outputOffset outputLength)
        (transport state) (shared state) result next nextShared) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state result (withTransport state next nextShared)

inductive Builtin (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    String → Ty → List Semantics.Value → State → Semantics.Result Semantics.Value → State → Prop where
  | runtime {name type arguments state result final}
      (computed : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments state.runtime result final) :
      Builtin children image name type arguments state result {state with runtime := final}
  | call {type state result final gas target value inputOffset inputLength outputOffset outputLength}
      (computed : Call children .ordinary gas target value inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "call" type [.word gas, .word target, .word value, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | staticCall {type state result final gas target inputOffset inputLength outputOffset outputLength}
      (computed : Call children .staticCall gas target Word.zero inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "staticcall" type [.word gas, .word target, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | callCode {type state result final gas target value inputOffset inputLength outputOffset outputLength}
      (computed : Call children .callCode gas target value inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "callcode" type [.word gas, .word target, .word value, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | delegateCall {type state result final gas target inputOffset inputLength outputOffset outputLength}
      (computed : Call children .delegateCall gas target ((observations state).direct .callvalue)
        inputOffset inputLength outputOffset outputLength state result final) :
      Builtin children image "delegatecall" type [.word gas, .word target, .word inputOffset,
        .word inputLength, .word outputOffset, .word outputLength] state result final
  | destroy {type state result final beneficiary}
      (computed : RuntimeLifecycleSemantics.Destroy beneficiary state result final) :
      Builtin children image "selfdestruct" type [.word beneficiary] state result final
  | create {type state result final value offset length}
      (computed : CreationSemantics.Refused value offset length state result final) :
      Builtin children image "create" type [.word value, .word offset, .word length] state result final
  | create2 {type state result final value offset length salt}
      (computed : CreationSemantics.Refused value offset length state result final) :
      Builtin children image "create2" type [.word value, .word offset, .word length, .word salt] state result final

def effectsWith (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics State where
  builtin := Builtin children image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State :=
  effectsWith (fun _ => AccountCallSemantics.noChildren) image

end Solcore.Frontend.RustHull.RuntimeCallModeSemantics
