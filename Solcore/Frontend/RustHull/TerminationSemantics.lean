import Solcore.Frontend.RustHull.RuntimeEffectsSemantics

/-! Independent message termination. A valid range expands memory, records the
exit and propagates the termination sentinel. An overflowing range faults before
any termination register changes; an empty range leaves memory size unchanged. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.TerminationSemantics
open Core

inductive Operation where
  | returned | reverted | stopped | invalid
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .returned => "return" | .reverted => "revert" | .stopped => "stop" | .invalid => "invalid"

def Operation.kind : Operation → Nat
  | .returned | .stopped => 1 | .reverted => 2 | .invalid => 3

def Operation.arity : Operation → Nat
  | .returned | .reverted => 2 | .stopped | .invalid => 0

def terminate (state : RuntimeEffectsSemantics.State) (kind : Nat) (offset length : Word) :
    Semantics.Result Semantics.Value × RuntimeEffectsSemantics.State :=
  match MemorySemantics.touchSize? state.memory.size offset length with
  | none => (MemorySemantics.overflow, state)
  | some size => (.fault (.language Word.maximum), {
      memory := {state.memory with size := size}
      storage := {state.storage with exit := Word.ofNatModulo kind, returnOffset := offset, returnSize := length}})

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : RuntimeEffectsSemantics.State) :
    Option (Semantics.Result Semantics.Value × RuntimeEffectsSemantics.State) :=
  if name = "return" then
    match arguments with
    | [.word offset, .word length] => some (terminate state 1 offset length)
    | _ => none
  else if name = "revert" then
    match arguments with
    | [.word offset, .word length] => some (terminate state 2 offset length)
    | _ => none
  else if name = "stop" then
    match arguments with
    | [] => some (terminate state 1 Word.zero Word.zero)
    | _ => none
  else if name = "invalid" then
    match arguments with
    | [] => some (terminate state 3 Word.zero Word.zero)
    | _ => none
  else none

def effects : Semantics.ExternalSemantics RuntimeEffectsSemantics.State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.TerminationSemantics
