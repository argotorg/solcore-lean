import Solcore.Core.WordMapping

/-! Byte-addressed memory expressed using the existing Core mapping and cells.
The memory cell contains a mapping from word indices to big-endian 32-byte
words. The size cell records the largest touched range, rounded up to 32.
Range overflow returns a language failure before changing memory or size. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Memory
open Core

def definitions : DataEnvironment := WordMapping.actualDefinitions
def memoryType : Ty := .cell WordMapping.type
def sizeType : Ty := .cell .word
def overflowReason : Word := Word.ofNatModulo 6

private def number (value : Nat) : Expr := .word (Word.ofNatModulo value)
private def add (left right : Expr) : Expr := .binary .wordAdd left right
private def sub (left right : Expr) : Expr := .binary .wordSub left right
private def index (offset : Expr) : Expr := .binary .wordDiv offset (number 32)
private def position (offset : Expr) : Expr := .binary .wordMod offset (number 32)
private def shift (offset : Expr) : Expr := .binary .wordMul (position offset) (number 8)
private def byte (value : Expr) : Expr := .binary .wordAnd value (number 255)

/-- Read one byte from packed memory entries. Raw calldata/code byte maps use
`WordMapping.lookupEntries` instead. -/
def lookupByte (entries : WordMapping.Entries) (offset : Word) : Word :=
  Word.byteAt (Word.ofNatModulo (offset.val % 32))
    (WordMapping.lookupEntries (Word.ofNatModulo (offset.val / 32)) entries)

private def insertByte (entries : WordMapping.Entries) (offset value : Word) : WordMapping.Entries :=
  let key := Word.ofNatModulo (offset.val / 32)
  let shift := Word.ofNatModulo ((31 - offset.val % 32) * 8)
  let mask := (Word.ofNatModulo 255).shiftLeft shift
  let old := WordMapping.lookupEntries key entries
  let updated := (old.bitAnd mask.bitNot).bitOr
    ((value.bitAnd (Word.ofNatModulo 255)).shiftLeft shift)
  WordMapping.insertEntries key updated entries

/-- Convert a raw byte mapping to packed memory. As with `lookupEntries`, the
first entry for a repeated byte address wins; byte values use their low 8 bits. -/
def packEntries (entries : WordMapping.Entries) : WordMapping.Entries :=
  entries.foldr (fun (offset, value) packed => insertByte packed offset value) []

/-- Pack bytes at an absolute byte offset. Bytes outside the Word address
space are omitted, so an overflowing suffix never wraps to address zero. -/
def packBytes (bytes : List UInt8) (offset : Nat := 0) : WordMapping.Entries :=
  packEntries (bytes.zipIdx.filterMap fun (byte, index) =>
    if offset + index < wordModulus then
      some (Word.ofNatModulo (offset + index), Word.ofNatModulo byte.toNat)
    else none)

private def packet : List Expr → Expr
  | [] => .unit
  | [value] => value
  | value :: rest => .pair value (packet rest)

private def field (index : Nat) : Nat → Expr → Expr
  | 0, _ => .unit
  | 1, value => value
  | count + 2, value => if index = 0 then .first value
      else field (index - 1) (count + 1) (.second value)

/-- Evaluate the size reference, offset and length once. A zero-length range
does not inspect or expand the size cell. An unrepresentable rounded size is
reported as overflow rather than wrapping to a smaller memory extent. -/
def touch (sizeReference offset length : Expr) : Expr :=
  .letE (packet [sizeReference, offset, length])
    (.ifE (.binary .wordEq (field 2 3 (.var 0)) (number 0))
      (LanguageResult.success .unit)
      (.letE (add (field 1 3 (.var 0)) (field 2 3 (.var 0)))
        (.ifE (.binary .wordGt (field 1 3 (.var 1)) (.var 0))
          (LanguageResult.failure .unit (.word overflowReason))
          (.ifE (.binary .wordGt (.var 0) (number (wordModulus - 32)))
            (LanguageResult.failure .unit (.word overflowReason))
            (.letE (.binary .wordMul
              (.binary .wordDiv (add (.var 0) (number 31)) (number 32)) (number 32))
              (LanguageResult.success
                (.ifE (.binary .wordGt (.var 0) (.loadCell (field 0 3 (.var 2))))
                  (.storeCell (field 0 3 (.var 2)) (.var 0)) .unit)))))))

/-- Read memory size without expanding it. -/
def msize (sizeReference : Expr) : Expr :=
  .letE sizeReference (LanguageResult.success (.loadCell (.var 0)))

private def readBytes : Nat → Expr → Expr → Expr → Expr
  | 0, _, _, accumulator => LanguageResult.success accumulator
  | count + 1, mapping, offset, accumulator =>
      let next := add (.binary .wordMul (accumulator.weakenAt 0) (number 256)) (byte (.var 0))
      LanguageResult.bind .word (WordMapping.lookup mapping offset)
        (.ifE (.binary .wordEq (offset.weakenAt 0) (number (wordModulus - 1)))
          (LanguageResult.success (.binary .wordMul next (number (256 ^ count))))
          (readBytes count (mapping.weakenAt 0) (add (offset.weakenAt 0) (number 1)) next))

/-- Read a word from a fixed byte mapping without updating memory size. This
also gives zero right padding for calldata whose missing entries are zero. -/
def readWord (mapping offset : Expr) : Expr :=
  .letE (.pair mapping offset) (readBytes 32 (.first (.var 0)) (.second (.var 0)) (number 0))

/-- Read a byte from a fixed mapping without touching a memory-size cell. -/
def readByte (mapping offset : Expr) : Expr :=
  LanguageResult.bind .word (WordMapping.lookup mapping offset)
    (LanguageResult.success (byte (.var 0)))

/-- Read a byte from a packed memory snapshot without expanding its size. -/
def readMemoryByte (mapping offset : Expr) : Expr :=
  .letE (.pair mapping offset)
    (LanguageResult.bind .word
      (WordMapping.lookup (.first (.var 0)) (index (.second (.var 0))))
      (LanguageResult.success (.binary .wordByte (position (.second (.var 1))) (.var 0))))

/-- Read a packed memory snapshot, combining at most two adjacent words.
An address beyond the last packed word is zero-padded without wrapping. -/
def readMemoryWord (mapping offset : Expr) : Expr :=
  .letE (.pair mapping offset)
    (LanguageResult.bind .word
      (WordMapping.lookup (.first (.var 0)) (index (.second (.var 0))))
      (.ifE (.binary .wordEq (position (.second (.var 1))) (number 0))
        (LanguageResult.success (.var 0))
        (LanguageResult.bind .word
          (.ifE (.binary .wordEq (index (.second (.var 1))) (number ((wordModulus - 1) / 32)))
            (LanguageResult.success (number 0))
            (WordMapping.lookup (.first (.var 1)) (add (index (.second (.var 1))) (number 1))))
          (LanguageResult.success (.binary .wordOr
            (.binary .wordShl (.var 1) (shift (.second (.var 2))))
            (.binary .wordShr (.var 0) (sub (number 256) (shift (.second (.var 2))))))))))

private def writeMemoryByte (mapping offset value : Expr) : Expr :=
  .letE (packet [mapping, offset, value])
    (.letE (.binary .wordMul (sub (number 31) (position (field 1 3 (.var 0)))) (number 8))
      (LanguageResult.bind WordMapping.type
        (WordMapping.lookup (field 0 3 (.var 1)) (index (field 1 3 (.var 1))))
        (WordMapping.insert (field 0 3 (.var 2)) (index (field 1 3 (.var 2)))
          (.binary .wordOr
            (.binary .wordAnd (.var 0) (.unary .wordNot (.binary .wordShl (number 255) (.var 1))))
            (.binary .wordShl (byte (field 2 3 (.var 2))) (.var 1))))))

private def writeMemoryWord (mapping offset value : Expr) : Expr :=
  .letE (packet [mapping, offset, value])
    (.ifE (.binary .wordEq (position (field 1 3 (.var 0))) (number 0))
      (WordMapping.insert (field 0 3 (.var 0)) (index (field 1 3 (.var 0))) (field 2 3 (.var 0)))
      (.letE (shift (field 1 3 (.var 0)))
        (.letE (.binary .wordShr (number (wordModulus - 1)) (.var 0))
          (LanguageResult.bind WordMapping.type
            (WordMapping.lookup (field 0 3 (.var 2)) (index (field 1 3 (.var 2))))
            (LanguageResult.bind WordMapping.type
              (WordMapping.insert (field 0 3 (.var 3)) (index (field 1 3 (.var 3)))
                (.binary .wordOr (.binary .wordAnd (.var 0) (.unary .wordNot (.var 1)))
                  (.binary .wordShr (field 2 3 (.var 3)) (.var 2))))
              (LanguageResult.bind WordMapping.type
                (WordMapping.lookup (.var 0) (add (index (field 1 3 (.var 4))) (number 1)))
                (WordMapping.insert (.var 1) (add (index (field 1 3 (.var 5))) (number 1))
                  (.binary .wordOr (.binary .wordAnd (.var 0) (.var 3))
                    (.binary .wordShl (field 2 3 (.var 5)) (sub (number 256) (.var 4)))))))))))

/-- Read 32 bytes in big-endian order, including unaligned offsets. Missing
mapping entries read as zero; reads expand the visible size just like writes. -/
def mload (memoryReference sizeReference offset : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset])
    (LanguageResult.bind .word (touch (field 1 3 (.var 0)) (field 2 3 (.var 0)) (number 32))
      (.letE (.loadCell (field 0 3 (.var 1)))
        (readMemoryWord (.var 0) (field 2 3 (.var 2)))))

/-- Read one byte and expand the touched range. -/
def loadByte (memoryReference sizeReference offset : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset])
    (LanguageResult.bind .word (touch (field 1 3 (.var 0)) (field 2 3 (.var 0)) (number 1))
      (readMemoryByte (.loadCell (field 0 3 (.var 1))) (field 2 3 (.var 1))))

/-- Write the 32 bytes of a word, with its most significant byte first. The
mapping update is published after all bytes have been prepared. -/
def mstore (memoryReference sizeReference offset value : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset, value])
    (LanguageResult.bind .unit (touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (number 32))
      (.letE (.loadCell (field 0 4 (.var 1)))
        (LanguageResult.bind .unit
          (writeMemoryWord (.var 0) (field 2 4 (.var 2)) (field 3 4 (.var 2)))
          (LanguageResult.success (.storeCell (field 0 4 (.var 3)) (.var 0))))))

/-- Store only the least significant byte. -/
def mstore8 (memoryReference sizeReference offset value : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, offset, value])
    (LanguageResult.bind .unit (touch (field 1 4 (.var 0)) (field 2 4 (.var 0)) (number 1))
      (LanguageResult.bind .unit
        (writeMemoryByte (.loadCell (field 0 4 (.var 1)))
          (field 2 4 (.var 1)) (field 3 4 (.var 1)))
        (LanguageResult.success (.storeCell (field 0 4 (.var 2)) (.var 0)))))

private def validRange (offset length : Expr) : Expr :=
  .ifE (.binary .wordEq length (number 0)) (.bool true)
    (.letE (add offset length)
      (.ifE (.binary .wordGt (offset.weakenAt 0) (.var 0)) (.bool false)
        (.unary .boolNot (.binary .wordGt (.var 0) (number (wordModulus - 32))))))

private def copyParameter : Ty :=
  .product WordMapping.type (.product .word (.product .word (.product .word memoryType)))

private def copyStep (packed : Bool) (width : Nat) : Expr :=
  let read := if packed then
    if width = 32 then readMemoryWord else readMemoryByte
    else if width = 32 then readWord else readByte
  let write := if width = 32 then writeMemoryWord else writeMemoryByte
  LanguageResult.bind .unit (read (field 0 5 (.var 0)) (field 2 5 (.var 0)))
      (LanguageResult.bind .unit
        (write (.loadCell (field 4 5 (.var 1))) (field 1 5 (.var 1)) (.var 0))
        (.letE (.storeCell (field 4 5 (.var 2)) (.var 0))
          (WordMapping.invoke copyParameter .unit (.var 4)
            (packet [.ifE (.binary .wordGt (field 2 5 (.var 3)) (number (wordModulus - 1 - width)))
                WordMapping.empty (field 0 5 (.var 3)), add (field 1 5 (.var 3)) (number width),
              add (field 2 5 (.var 3)) (number width),
              sub (field 3 5 (.var 3)) (number width), field 4 5 (.var 3)]))))

private def copyBody (packed : Bool) : Expr :=
  .ifE (.binary .wordEq (field 3 5 (.var 0)) (number 0))
    (LanguageResult.success .unit)
    (.ifE (.binary .wordGt (field 3 5 (.var 0)) (number 31))
      (copyStep packed 32) (copyStep packed 1))

/-- Copy from a retained source mapping, so both directions of overlapping
ranges behave like memmove. Validate both ranges before touching either one.
The dynamic loop runs on Core and can suspend and resume with ordinary fuel. -/
def mcopy (memoryReference sizeReference destination source length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, destination, source, length])
    (.ifE (validRange (field 2 5 (.var 0)) (field 4 5 (.var 0)))
      (.ifE (validRange (field 3 5 (.var 0)) (field 4 5 (.var 0)))
        (LanguageResult.bind .unit (touch (field 1 5 (.var 0)) (field 2 5 (.var 0)) (field 4 5 (.var 0)))
          (LanguageResult.bind .unit (touch (field 1 5 (.var 1)) (field 3 5 (.var 1)) (field 4 5 (.var 1)))
            (WordMapping.runHelper copyParameter .unit (copyBody true)
              (packet [.loadCell (field 0 5 (.var 2)), field 2 5 (.var 2),
                field 3 5 (.var 2), field 4 5 (.var 2), field 0 5 (.var 2)]))))
        (LanguageResult.failure .unit (.word overflowReason)))
      (LanguageResult.failure .unit (.word overflowReason)))

/-- Copy a fixed byte mapping such as calldata into memory. Only the
destination expands memory. Out-of-range source bytes are zero, including the
suffix past the largest Word offset, which must not wrap to source byte zero. -/
def copyFrom (memoryReference sizeReference destination sourceMapping sourceOffset length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, destination, sourceMapping, sourceOffset, length])
    (LanguageResult.bind .unit
      (touch (field 1 6 (.var 0)) (field 2 6 (.var 0)) (field 5 6 (.var 0)))
      (WordMapping.runHelper copyParameter .unit (copyBody false)
        (packet [field 3 6 (.var 1), field 2 6 (.var 1), field 4 6 (.var 1),
          field 5 6 (.var 1), field 0 6 (.var 1)])))

/-- Copy a packed calldata/code snapshot into memory, in word-sized chunks
followed by any tail bytes. Only the destination expands memory. -/
def copyPackedFrom (memoryReference sizeReference destination sourceMapping sourceOffset length : Expr) : Expr :=
  .letE (packet [memoryReference, sizeReference, destination, sourceMapping, sourceOffset, length])
    (LanguageResult.bind .unit
      (touch (field 1 6 (.var 0)) (field 2 6 (.var 0)) (field 5 6 (.var 0)))
      (WordMapping.runHelper copyParameter .unit (copyBody true)
        (packet [field 3 6 (.var 1), field 2 6 (.var 1), field 4 6 (.var 1),
          field 5 6 (.var 1), field 0 6 (.var 1)])))

end Solcore.Frontend.RustHull.Memory
