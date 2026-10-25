import Solcore.Frontend.RustHull.Semantics

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
