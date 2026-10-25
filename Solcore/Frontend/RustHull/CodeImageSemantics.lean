import Solcore.Frontend.RustHull.MemoryCopySemantics
import Solcore.Frontend.RustHull.Memory

/-! Copying the current object's immutable code image uses packed source bytes.
The supplied image is an execution parameter and does not add mutable state. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CodeImageSemantics
open Core

inductive Operation where
  | codeCopy | dataCopy
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .codeCopy => "codecopy"
  | .dataCopy => "datacopy"

theorem Operation.name_injective : Function.Injective Operation.name := by
  intro first second same
  cases first <;> cases second <;> simp_all [Operation.name]

def unavailable : Semantics.Result Semantics.Value := .fault (.language (Word.ofNatModulo 15))

inductive Execute (image : Option (List UInt8)) (destination source length : Word) :
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | unknown {state : MemorySemantics.State} (absent : image = none) :
      Execute image destination source length state unavailable state
  | copied {bytes : List UInt8} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (present : image = some bytes)
      (executed : MemoryCopySemantics.From (Memory.packBytes bytes) destination source length initial result final) :
      Execute image destination source length initial result final

inductive Builtin (image : Option (List UInt8)) : String → Ty → List Semantics.Value →
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | copy (operation : Operation) {type : Ty} {destination source length : Word}
      {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
      (executed : Execute image destination source length initial result final) :
      Builtin image operation.name type [.word destination, .word source, .word length] initial result final

theorem Builtin.named {image : Option (List UInt8)} {name : String} {type : Ty}
    {arguments : List Semantics.Value} {initial final : MemorySemantics.State} {result : Semantics.Result Semantics.Value}
    (called : Builtin image name type arguments initial result final) :
    ∃ operation : Operation, operation.name = name := by
  cases called with
  | copy operation _ => exact ⟨operation, rfl⟩

end Solcore.Frontend.RustHull.CodeImageSemantics
