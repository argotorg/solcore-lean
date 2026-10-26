import Solcore.Frontend.RustHull.RuntimeCallEffectsSemantics

/-! Hull's explicit revert, independently of its lowering. The message holds at
most one EVM word of UTF-8 bytes. As in the pinned Yul backend, it is stored
left-aligned as one word at memory offset zero, and the frame reverts with
exactly the message bytes. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.RevertSemantics
open Core

/-- The big-endian value of a byte string. -/
def bytesValue : List UInt8 → Nat
  | [] => 0
  | byte :: rest => byte.toNat * 256 ^ rest.length + bytesValue rest

/-- The message bytes left-aligned in one word. -/
def messageWord (message : String) : Word :=
  Word.ofNatModulo (bytesValue message.toUTF8.data.toList * 256 ^ (32 - message.toUTF8.size))

/-- The number of message bytes. -/
def messageLength (message : String) : Word := Word.ofNatModulo message.toUTF8.size

/-- The frame stores the message word at offset zero and then reverts with the
message bytes; the termination sentinel stops the frame. -/
inductive Reverted (message : String) (state : RuntimeCallEffectsSemantics.State) :
    Semantics.Control → RuntimeCallEffectsSemantics.State → Prop where
  | reverted {memory : MemorySemantics.State} {reason : Semantics.Fault} {halted : RuntimeEffectsSemantics.State}
      (fits : message.toUTF8.size ≤ 32)
      (stored : MemorySemantics.mstore state.runtime.runtime.runtime.runtime.runtime.memory Word.zero
        (messageWord message) = (.value .unit, memory))
      (terminated : TerminationSemantics.terminate {state.runtime.runtime.runtime.runtime.runtime with memory := memory}
        2 Word.zero (messageLength message) = (.fault reason, halted)) :
      Reverted message state (.fault reason)
        {state with runtime := RuntimeReturnDataEffectsSemantics.withRuntime state.runtime halted}

end Solcore.Frontend.RustHull.RevertSemantics
