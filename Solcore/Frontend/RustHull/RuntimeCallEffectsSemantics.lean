import Solcore.Frontend.RustHull.RuntimeCallStateSemantics
import Solcore.Frontend.RustHull.CallTransportSemantics

/-! Ordinary and static message calls compose account dispatch with caller
transport. Child execution is an explicit source relation; the first public
instance uses noChildren, and finite call trees can supply recursively checked
source frames without changing the Hull expression rules. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
open Core

inductive Operation where
  | ordinary | staticCall
  deriving DecidableEq, BEq, Repr

def Operation.name : Operation → String
  | .ordinary => "call" | .staticCall => "staticcall"

def transport (state : State) : CallTransportSemantics.State :=
  ⟨state.runtime.runtime.runtime.runtime.runtime.memory, state.runtime.returnData,
    RuntimeReturnDataEffectsSemantics.size state.runtime⟩

def withTransport (state : State) (next : CallTransportSemantics.State)
    (shared : AccountCallSemantics.Shared) : State :=
  withReturned (withShared state shared) next.memory next.returnData next.returnDataSize

def arguments (operation : Operation) (state : State)
    (gas target value inputOffset inputLength outputOffset outputLength : Word) : CallTransportSemantics.Arguments :=
  let runtime := state.runtime.runtime.runtime.runtime.runtime
  {caller := runtime.storage.address, depth := state.callDepth
   isStatic := if operation = .staticCall then true else runtime.storage.isStatic
   gas := if operation = .ordinary ∧ value ≠ Word.zero then gas.add (Word.ofNatModulo 2300) else gas
   target := target, value := value, inputOffset := inputOffset, inputLength := inputLength
   outputOffset := outputOffset, outputLength := outputLength}

def invalid (state : State) : Semantics.Result Semantics.Value × State :=
  let stopped := TerminationSemantics.terminate state.runtime.runtime.runtime.runtime.runtime 3 Word.zero Word.zero
  (stopped.1, {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime stopped.2})

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
      (ordinary : operation = .ordinary)
      (notStatic : state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (nonzero : value ≠ Word.zero)
      (overflow : gas > Word.ofNatModulo (wordModulus - 2301)) :
      Call children operation gas target value inputOffset inputLength outputOffset outputLength
        state (.fault (.language (Word.ofNatModulo 13))) state
  | invoked {state : State} {next : CallTransportSemantics.State} {nextShared : AccountCallSemantics.Shared}
      {result : Semantics.Result Semantics.Value}
      (permitted : operation = .staticCall ∨ value = Word.zero ∨
        state.runtime.runtime.runtime.runtime.runtime.storage.isStatic = false)
      (stipend : operation = .ordinary → value ≠ Word.zero →
        ¬gas > Word.ofNatModulo (wordModulus - 2301))
      (executed : CallTransportSemantics.Execute
        (AccountCallSemantics.Dispatch (children state) .ordinary state.runtime.runtime.runtime.runtime.runtime.storage.address)
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

def effectsWith (children : State → AccountCallSemantics.Children) (image : Option (List UInt8)) :
    Semantics.ExternalSemantics State where
  builtin := Builtin children image
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

/-- Height zero permits local account outcomes, including an empty-account
call, while ruling out execution of another Hull frame. -/
def effects (image : Option (List UInt8)) : Semantics.ExternalSemantics State :=
  effectsWith (fun _ => AccountCallSemantics.noChildren) image

theorem runtime_balances {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : RuntimeReturnDataEffectsSemantics.State}
    {result : Semantics.Result Semantics.Value}
    (called : RuntimeReturnDataEffectsSemantics.Builtin image name type arguments initial result final) :
    final.runtime.balances = initial.runtime.balances := by
  cases called with
  | guard _ => rfl
  | copy _ => rfl
  | runtime called =>
      cases called with
      | copy _ => rfl
      | runtime called =>
          cases called <;> rfl

end Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics
