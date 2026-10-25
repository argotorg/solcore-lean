import Solcore.Frontend.RustHull.MemoryCopySemantics

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
