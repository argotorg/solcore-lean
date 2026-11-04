import Solcore.Frontend.RustHull.Semantics

/-!
# Hull memory semantics

Byte memory, range copies, the memory guard and memory snapshots. Main declarations:
`MemorySemantics.State`, `MemorySemantics.builtin`, `MemoryCopySemantics.Operation`,
`MemorySnapshotSemantics`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.MemorySemantics
/-! Independent packed-word memory for Hull effects. Addresses count bytes,
words are big-endian, and missing entries are zero. The definitions use only
source values and mathematical word operations. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.MemorySemantics
open Core

abbrev Entries := List (Word × Word)

def lookup (key : Word) : Entries → Word
  | [] => Word.zero
  | (storedKey, value) :: rest => if key == storedKey then value else lookup key rest

def insert (key value : Word) : Entries → Entries
  | [] => [(key, value)]
  | (storedKey, storedValue) :: rest =>
      if key == storedKey then (key, value) :: rest
      else (storedKey, storedValue) :: insert key value rest

structure State where
  words : Entries := []
  size : Word := Word.zero
  deriving Repr, BEq, DecidableEq

def index (offset : Word) : Word := offset.udiv (Word.ofNatModulo 32)
def position (offset : Word) : Word := offset.umod (Word.ofNatModulo 32)
def shift (offset : Word) : Word := (position offset).mul (Word.ofNatModulo 8)
def rounded (last : Word) : Word :=
  ((last.add (Word.ofNatModulo 31)).udiv (Word.ofNatModulo 32)).mul (Word.ofNatModulo 32)

/-- Empty ranges leave memory untouched. A nonempty range must have both its
end and its size rounded to 32 bytes representable without address wrap. -/
def touchSize? (size offset length : Word) : Option Word :=
  if length == Word.zero then some size
  else
    let last := offset.add length
    if offset > last then none
    else if last > Word.ofNatModulo (wordModulus - 32) then none
    else some (if rounded last > size then rounded last else size)

def readWord (entries : Entries) (offset : Word) : Word :=
  let first := lookup (index offset) entries
  if position offset == Word.zero then first
  else
    let second := if index offset == Word.ofNatModulo ((wordModulus - 1) / 32)
      then Word.zero else lookup ((index offset).add (Word.ofNatModulo 1)) entries
    (first.shiftLeft (shift offset)).bitOr
      (second.shiftRight ((Word.ofNatModulo 256).sub (shift offset)))

def writeWord (entries : Entries) (offset value : Word) : Entries :=
  if position offset == Word.zero then insert (index offset) value entries
  else
    let distance := shift offset
    let mask := (Word.ofNatModulo (wordModulus - 1)).shiftRight distance
    let first := lookup (index offset) entries
    let entries := insert (index offset)
      ((first.bitAnd mask.bitNot).bitOr (value.shiftRight distance)) entries
    let next := (index offset).add (Word.ofNatModulo 1)
    let second := lookup next entries
    insert next ((second.bitAnd mask).bitOr
      (value.shiftLeft ((Word.ofNatModulo 256).sub distance))) entries

def writeByte (entries : Entries) (offset value : Word) : Entries :=
  let distance := ((Word.ofNatModulo 31).sub (position offset)).mul (Word.ofNatModulo 8)
  let mask := (Word.ofNatModulo 255).shiftLeft distance
  let old := lookup (index offset) entries
  insert (index offset) ((old.bitAnd mask.bitNot).bitOr
    ((value.bitAnd (Word.ofNatModulo 255)).shiftLeft distance)) entries

def overflow : Semantics.Result Semantics.Value :=
  .fault (.language (Word.ofNatModulo 6))

def mload (state : State) (offset : Word) : Semantics.Result Semantics.Value × State :=
  match touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => (overflow, state)
  | some size => (.value (.word (readWord state.words offset)), {state with size := size})

def mstore (state : State) (offset value : Word) : Semantics.Result Semantics.Value × State :=
  match touchSize? state.size offset (Word.ofNatModulo 32) with
  | none => (overflow, state)
  | some size => (.value .unit, ⟨writeWord state.words offset value, size⟩)

def mstore8 (state : State) (offset value : Word) : Semantics.Result Semantics.Value × State :=
  match touchSize? state.size offset (Word.ofNatModulo 1) with
  | none => (overflow, state)
  | some size => (.value .unit, ⟨writeByte state.words offset value, size⟩)

def builtin (name : String) (_type : Ty) (arguments : List Semantics.Value)
    (state : State) : Option (Semantics.Result Semantics.Value × State) :=
  match name, arguments with
  | "msize", [] => some (.value (.word state.size), state)
  | "mload", [.word offset] => some (mload state offset)
  | "mstore", [.word offset, .word value] => some (mstore state offset value)
  | "mstore8", [.word offset, .word value] => some (mstore8 state offset value)
  | _, _ => none

def effects : Semantics.ExternalSemantics State where
  builtin := fun name type arguments initial result final =>
    builtin name type arguments initial = some (result, final)
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.MemorySemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryCopySemantics
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemoryGuardSemantics
/-! A memory guard supplies the same word to its caller. It carries no runtime
state transition in the independent Hull semantics. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemoryGuardSemantics

inductive Builtin : String → Ty → List Semantics.Value → Semantics.Result Semantics.Value → Prop where
  | guarded {type : Ty} {value : Core.Word} :
      Builtin "memoryguard" type [.word value] (.value (.word value))

theorem Builtin.named {name : String} {type : Ty} {arguments : List Semantics.Value}
    {result : Semantics.Result Semantics.Value} (called : Builtin name type arguments result) :
    name = "memoryguard" := by
  cases called
  rfl

end Solcore.Frontend.RustHull.MemoryGuardSemantics
end

section
-- leanmerge: from Solcore.Frontend.RustHull.MemorySnapshotSemantics
/-! A retained memory range starts at byte zero. Aligned extraction preserves
entry order and duplicate keys; the last word is padded with zero bytes.
Unaligned extraction uses the independently specified byte-copy relation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.MemorySnapshotSemantics
open Core
abbrev Entries := MemorySemantics.Entries

def lastIndex (length : Word) : Word := (length.sub (Word.ofNatModulo 1)).udiv (Word.ofNatModulo 32)
def padding (length : Word) : Word :=
  (((Word.ofNatModulo 32).sub (length.umod (Word.ofNatModulo 32))).umod (Word.ofNatModulo 32)).mul (Word.ofNatModulo 8)

def retain (start last shift : Word) : Entries → Entries
  | [] => []
  | (key, value) :: rest =>
      let retained := retain start last shift rest
      if start > key then retained
      else if key > Word.ofNatModulo ((wordModulus - 1) / 32) then retained
      else
        let rebased := key.sub start
        if rebased > last then retained
        else (rebased, if rebased == last then (value.shiftRight shift).shiftLeft shift else value) :: retained

def aligned (entries : Entries) (offset length : Word) : Entries :=
  retain (offset.udiv (Word.ofNatModulo 32)) (lastIndex length) (padding length) entries

inductive Extract (entries : Entries) (offset length : Word) : Semantics.Result Entries → Prop where
  | overflow (invalid : MemorySemantics.touchSize? Word.zero Word.zero length = none) :
      Extract entries offset length (.fault (.language (Word.ofNatModulo 6)))
  | empty (zero : length = Word.zero) : Extract entries offset length (.value [])
  | aligned {size : Word}
      (checked : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
      (nonempty : length ≠ Word.zero)
      (alignedOffset : offset.umod (Word.ofNatModulo 32) = Word.zero) :
      Extract entries offset length (.value (aligned entries offset length))
  | copied {size : Word} {result : Entries}
      (checked : MemorySemantics.touchSize? Word.zero Word.zero length = some size)
      (nonempty : length ≠ Word.zero)
      (unaligned : offset.umod (Word.ofNatModulo 32) ≠ Word.zero)
      (copied : MemoryCopySemantics.Copy entries Word.zero offset length [] result) :
      Extract entries offset length (.value result)

end Solcore.Frontend.RustHull.MemorySnapshotSemantics
end
