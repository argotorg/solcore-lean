import Solcore.Frontend.RustHull.MemorySemantics

/-! Independent event capture. The stream contains word-sized headers and
zero-padded payload snapshots. The copy relation describes byte ranges using
only mathematical words and source memory; it contains no compiled code. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.LogsSemantics
open Core

abbrev Words := MemorySemantics.Entries

def wordCount (length : Word) : Word :=
  (length.udiv (Word.ofNatModulo 32)).add
    (if length.umod (Word.ofNatModulo 32) == Word.zero then Word.zero else Word.ofNatModulo 1)

def chunk (length : Word) : Word :=
  if length > Word.ofNatModulo 31 then Word.ofNatModulo 32 else length

def padding (length : Word) : Word :=
  ((Word.ofNatModulo 32).sub (chunk length)).mul (Word.ofNatModulo 8)

def paddedWord (memory : Words) (offset length : Word) : Word :=
  ((MemorySemantics.readWord memory offset).shiftRight (padding length)).shiftLeft (padding length)

def insertWords (mapping : Words) (cursor : Word) : List Word → Words
  | [] => mapping
  | value :: rest => insertWords (MemorySemantics.insert cursor value mapping)
      (cursor.add (Word.ofNatModulo 1)) rest

/-- Payload words are copied from one immutable memory snapshot. Each step
advances by the actual number of bytes in its word and clears trailing bytes. -/
inductive Copy (memory : Words) : Word → Word → Words → Word → Words → Prop where
  | empty (offset cursor : Word) (mapping : Words) : Copy memory offset Word.zero mapping cursor mapping
  | step {offset length cursor : Word} {mapping result : Words}
      (nonempty : length ≠ Word.zero)
      (rest : Copy memory (offset.add (chunk length)) (length.sub (chunk length))
        (MemorySemantics.insert cursor (paddedWord memory offset length) mapping)
        (cursor.add (Word.ofNatModulo 1)) result) :
      Copy memory offset length mapping cursor result

structure State where
  memory : MemorySemantics.State := {}
  words : Words := []
  cursor : Word := Word.zero
  address : Word := Word.zero
  isStatic : Bool := false
  exit : Word := Word.zero
  returnOffset : Word := Word.zero
  returnSize : Word := Word.zero
  deriving Repr

def nextCursor (cursor length : Word) (topics : List Word) : Word :=
  cursor.add ((Word.ofNatModulo (3 + topics.length)).add (wordCount length))

def headers (address length : Word) (topics : List Word) : List Word :=
  [address, Word.ofNatModulo topics.length, length] ++ topics

inductive Append (offset length : Word) (topics : List Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | topics {state : State} (tooMany : topics.length > 4) :
      Append offset length topics state (.fault (.language (Word.ofNatModulo 11))) state
  | capacity {state : State} (allowed : topics.length ≤ 4)
      (overflow : state.cursor > nextCursor state.cursor length topics) :
      Append offset length topics state (.fault (.language (Word.ofNatModulo 10))) state
  | memory {state : State} (allowed : topics.length ≤ 4)
      (capacity : ¬state.cursor > nextCursor state.cursor length topics)
      (overflow : MemorySemantics.touchSize? state.memory.size offset length = none) :
      Append offset length topics state MemorySemantics.overflow state
  | done {state : State} {size : Word} {words : Words} (allowed : topics.length ≤ 4)
      (capacity : ¬state.cursor > nextCursor state.cursor length topics)
      (expanded : MemorySemantics.touchSize? state.memory.size offset length = some size)
      (copied : Copy state.memory.words offset length
        (insertWords state.words state.cursor (headers state.address length topics))
        (state.cursor.add (Word.ofNatModulo (3 + topics.length))) words) :
      Append offset length topics state (.value .unit)
        {state with
          memory := {state.memory with size := size}
          words := words
          cursor := nextCursor state.cursor length topics}

inductive Operation where | log0 | log1 | log2 | log3 | log4
  deriving DecidableEq

def Operation.name : Operation → String
  | .log0 => "log0" | .log1 => "log1" | .log2 => "log2" | .log3 => "log3" | .log4 => "log4"

def Operation.count : Operation → Nat
  | .log0 => 0 | .log1 => 1 | .log2 => 2 | .log3 => 3 | .log4 => 4

inductive Execute (offset length : Word) (topics : List Word) :
    State → Semantics.Result Semantics.Value → State → Prop where
  | static {state : State} (readOnly : state.isStatic = true) :
      Execute offset length topics state (.fault (.language Word.maximum))
        {state with exit := Word.ofNatModulo 3, returnOffset := Word.zero, returnSize := Word.zero}
  | writable {state final : State} {result : Semantics.Result Semantics.Value}
      (writable : state.isStatic = false) (appended : Append offset length topics state result final) :
      Execute offset length topics state result final

inductive Builtin : String → Ty → List Semantics.Value →
    State → Semantics.Result Semantics.Value → State → Prop where
  | log (operation : Operation) (type : Ty) (offset length : Word) (topics : List Word)
      {initial final : State} {result : Semantics.Result Semantics.Value}
      (count : topics.length = operation.count)
      (executed : Execute offset length topics initial result final) :
      Builtin operation.name type (.word offset :: .word length :: topics.map Semantics.Value.word) initial result final

def effects : Semantics.ExternalSemantics State where
  builtin := Builtin
  assembly := fun _ _ _ _ _ _ => False
  revert := fun _ _ _ _ => False

end Solcore.Frontend.RustHull.LogsSemantics
