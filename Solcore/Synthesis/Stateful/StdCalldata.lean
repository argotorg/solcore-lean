import Solcore.Synthesis.Core.StdDispatch
import Solcore.ContractRuntime.CheckedCoreContract

/-! A second model of the pinned std's dispatcher and lazy calldata decoder,
written over the calldata bytes instead of in Core and shared by the
malformed-calldata profiles. Natural arithmetic cannot wrap, as std's checked
word arithmetic does not. The changes every malformation shares are applied to
a canonical encoding here; each profile names the positions of its own Words. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Stateful.StdCalldata
open Solcore.Core (Word)
open Solcore.ContractRuntime (encodeWordBytesBE encodeBytesText)
open Solcore.Synthesis.Core.StdDispatch (noSelectorError truncatedError maxLength)

/-- Calldata of every transaction stays within one KiB. -/
def maxCalldata : Nat := 1024

/-- The byte at an index, zero past the end; callers read only present bytes. -/
def byteAt (bytes : ByteArray) (index : Nat) : Nat :=
  (bytes.data[index]?.map UInt8.toNat).getD 0

def bigEndian (bytes : ByteArray) (offset count : Nat) : Nat :=
  (List.range count).foldl (fun total index => total * 256 + byteAt bytes (offset + index)) 0

def wordAt (bytes : ByteArray) (offset : Nat) : Nat := bigEndian bytes offset 32

def replaceWord (bytes : ByteArray) (offset : Nat) (value : Word) : ByteArray :=
  bytes.extract 0 offset ++ encodeWordBytesBE value ++ bytes.extract (offset + 32) bytes.size

/-- Trailing bytes are zeros (0), `0xff` (1) or the ramp `1, 2, 3, ...` (2). -/
def patternNames : List String := ["zeros", "ones", "ramp"]

def patternByte (pattern position : Nat) : UInt8 :=
  match pattern with
  | 0 => 0
  | 1 => 0xff
  | _ => (position + 1).toUInt8

/-- The change a malformation makes to a canonical encoding: none, a prefix of
the selector, a selector xor mask, a cut, trailing bytes, or one replaced Word
at a byte position. -/
inductive Change where
  | none
  | short (bytes : Nat)
  | selector (mask : Nat)
  | truncate (kept : Nat)
  | trailing (count pattern : Nat)
  | word (position : Nat) (value : Word)
  deriving BEq, Repr

def Change.apply (canonical : ByteArray) : Change → ByteArray
  | .none => canonical
  | .short bytes => canonical.extract 0 bytes
  | .selector mask =>
      let changed := (bigEndian canonical 0 4 ^^^ mask) % 2 ^ 32
      ByteArray.mk #[(changed / 2 ^ 24 % 256).toUInt8, (changed / 2 ^ 16 % 256).toUInt8,
        (changed / 2 ^ 8 % 256).toUInt8, (changed % 256).toUInt8] ++ canonical.extract 4 canonical.size
  | .truncate kept => canonical.extract 0 kept
  | .trailing count pattern => canonical ++ ByteArray.mk ((List.range count).map (patternByte pattern)).toArray
  | .word position value => replaceWord canonical position value

/-- A change within its bounds: selector prefixes, nonzero 32-bit masks, cuts
inside the calldata past the selector, one to 64 trailing bytes, and a Word
replaced inside the canonical encoding. -/
def Change.valid (canonicalSize : Nat) : Change → Bool
  | .none => true
  | .short bytes => bytes < 4
  | .selector mask => 0 < mask && mask < 2 ^ 32
  | .truncate kept => 4 ≤ kept && kept < canonicalSize
  | .trailing count pattern => 1 ≤ count && count ≤ 64 && pattern < 3
  | .word position _ => 4 ≤ position && position + 32 ≤ canonicalSize

/-- An error selector as its four bytes. -/
def selectorText (selector : Nat) : String :=
  encodeBytesText (ByteArray.mk #[(selector / 2 ^ 24 % 256).toUInt8, (selector / 2 ^ 16 % 256).toUInt8,
    (selector / 2 ^ 8 % 256).toUInt8, (selector % 256).toUInt8])

/-- std's dispatch and the head of `(uint256 flags, T value)` for a dynamic
`T`: the flags and the head offset `o`, once the default fallback is not
reached, the 64-byte head exists, `o <= size - 4` and 32 bytes remain at
`4 + o`. Otherwise the rejecting error selector. -/
def dynamicHead? (input : ByteArray) (selector : Nat) : Except Nat (Nat × Nat) :=
  let size := input.size
  if size < 4 then .error noSelectorError
  else if bigEndian input 0 4 != selector then .error noSelectorError
  else if size < 68 then .error truncatedError
  else
    let offset := wordAt input 36
    if offset > size - 4 then .error truncatedError
    else if size - (4 + offset) < 32 then .error truncatedError
    else .ok (wordAt input 4, offset)

/-- std's `checkArrayHead` for 32-byte elements, for an array whose length
Word is the 32 bytes at `start`: the length, once it is at most `~0 / 32` and
its elements fit after the length Word. -/
def arrayAt? (input : ByteArray) (start : Nat) : Except Nat Nat :=
  let length := wordAt input start
  if length > maxLength then .error truncatedError
  else if 32 * length > input.size - (start + 32) then .error truncatedError
  else .ok length

/-- std's lazy decode of row `index` of a dynamic-element array whose offset
table starts at `table`: the row's start and length, once its table Word `r`
satisfies `r <= size - table`, 32 bytes remain at `table + r` and the row passes
`arrayAt?`. -/
def rowAt? (input : ByteArray) (table index : Nat) : Except Nat (Nat × Nat) := do
  let size := input.size
  let entry := wordAt input (table + 32 * index)
  if entry > size - table then throw truncatedError
  if size - (table + entry) < 32 then throw truncatedError
  let length ← arrayAt? input (table + entry)
  return (table + entry, length)

end Solcore.Synthesis.Stateful.StdCalldata
