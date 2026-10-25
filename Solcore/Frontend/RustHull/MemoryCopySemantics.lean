import Solcore.Frontend.RustHull.MemorySemantics

/-! Memory copying reads a retained source snapshot. The source address never
wraps back to its first byte, and destination writes preserve their order. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryCopySemantics
open Core

def validRange (offset length : Word) : Bool :=
  if length == Word.zero then true
  else
    let last := offset.add length
    if offset > last then false
    else !(last > Word.ofNatModulo (wordModulus - 32))

def width (length : Word) : Nat := if length > Word.ofNatModulo 31 then 32 else 1

def readByte (words : MemorySemantics.Entries) (offset : Word) : Word :=
  Word.byteAt (MemorySemantics.position offset)
    (MemorySemantics.lookup (MemorySemantics.index offset) words)

def copiedWord (words : MemorySemantics.Entries) (source length : Word) : Word :=
  if length > Word.ofNatModulo 31 then MemorySemantics.readWord words source
  else readByte words source

def written (words : MemorySemantics.Entries) (destination length value : Word) :
    MemorySemantics.Entries :=
  if length > Word.ofNatModulo 31 then MemorySemantics.writeWord words destination value
  else MemorySemantics.writeByte words destination value

def remainingSource (words : MemorySemantics.Entries) (source length : Word) :
    MemorySemantics.Entries :=
  if source > Word.ofNatModulo (wordModulus - 1 - width length) then [] else words

/-- The retained source mapping is distinct from the changing destination.
This also specifies both directions of overlapping memory copies. -/
inductive Copy : MemorySemantics.Entries → Word → Word → Word →
    MemorySemantics.Entries → MemorySemantics.Entries → Prop where
  | empty (sourceWords destinationWords : MemorySemantics.Entries) (destination source : Word) :
      Copy sourceWords destination source Word.zero destinationWords destinationWords
  | step {sourceWords destinationWords finalWords : MemorySemantics.Entries}
      {destination source length : Word}
      (nonempty : length ≠ Word.zero)
      (rest : Copy (remainingSource sourceWords source length)
        (destination.add (Word.ofNatModulo (width length)))
        (source.add (Word.ofNatModulo (width length)))
        (length.sub (Word.ofNatModulo (width length)))
        (written destinationWords destination length (copiedWord sourceWords source length)) finalWords) :
      Copy sourceWords destination source length destinationWords finalWords

/-- Copying an immutable input expands only the destination range. -/
inductive From (sourceWords : MemorySemantics.Entries) (destination source length : Word) :
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | overflow {initial : MemorySemantics.State}
      (touched : MemorySemantics.touchSize? initial.size destination length = none) :
      From sourceWords destination source length initial MemorySemantics.overflow initial
  | done {initial : MemorySemantics.State} {size : Word} {words : MemorySemantics.Entries}
      (touched : MemorySemantics.touchSize? initial.size destination length = some size)
      (copied : Copy sourceWords destination source length initial.words words) :
      From sourceWords destination source length initial (.value .unit) ⟨words, size⟩

/-- Both ranges are checked before a memory-to-memory copy changes either the
memory size or its words. The source is captured after the two range touches. -/
inductive Move (destination source length : Word) :
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | destinationOverflow (initial : MemorySemantics.State)
      (invalid : validRange destination length = false) :
      Move destination source length initial MemorySemantics.overflow initial
  | sourceOverflow (initial : MemorySemantics.State)
      (destinationValid : validRange destination length = true)
      (invalid : validRange source length = false) :
      Move destination source length initial MemorySemantics.overflow initial
  | done {initial : MemorySemantics.State} {destinationSize size : Word}
      {words : MemorySemantics.Entries}
      (destinationValid : validRange destination length = true)
      (sourceValid : validRange source length = true)
      (destinationTouched : MemorySemantics.touchSize? initial.size destination length = some destinationSize)
      (sourceTouched : MemorySemantics.touchSize? destinationSize source length = some size)
      (copied : Copy initial.words destination source length initial.words words) :
      Move destination source length initial (.value .unit) ⟨words, size⟩

inductive Operation where
  | move | calldata
  deriving DecidableEq, Repr

def Operation.name : Operation → String
  | .move => "mcopy"
  | .calldata => "calldatacopy"

inductive Builtin (calldata : MemorySemantics.Entries) : String → Ty → List Semantics.Value →
    MemorySemantics.State → Semantics.Result Semantics.Value → MemorySemantics.State → Prop where
  | move {type : Ty} {destination source length : Word} {initial final : MemorySemantics.State}
      {result : Semantics.Result Semantics.Value}
      (executed : Move destination source length initial result final) :
      Builtin calldata "mcopy" type [.word destination, .word source, .word length] initial result final
  | calldata {type : Ty} {destination source length : Word} {initial final : MemorySemantics.State}
      {result : Semantics.Result Semantics.Value}
      (executed : From calldata destination source length initial result final) :
      Builtin calldata "calldatacopy" type [.word destination, .word source, .word length] initial result final

end Solcore.Frontend.RustHull.MemoryCopySemantics
