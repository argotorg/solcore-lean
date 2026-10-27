import Solcore.Core.Primitive
import Solcore.Core.Wire.Codec.Program

/-! Core expressions for the pinned std's dispatcher and calldata decoder,
shared by the std-modeling wrappers of malformed calldata. Calldata is read
through the exact input host functions: `inputDataSize`, `inputDataByte?` and
`inputDataWordBE?`, which yields a Word only when all 32 bytes exist. A std
rejection reverts with its error selector as the Word payload. Each check
compares before it forms a sum or product, so no checked arithmetic wraps, as
std's checks do not. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.StdDispatch

open Solcore.Core (Word)
open Solcore.Core.Wire

/-- std's `NoSelectorMatchedWithoutFallback()`, reverted by the default fallback. -/
def noSelectorError : Nat := 0x4924aef0

/-- std's `ABIInputTruncated()`, reverted by every bounded calldata read. -/
def truncatedError : Nat := 0x08638556

/-- The largest length std admits for 32-byte elements, `~0 / 32`. -/
def maxLength : Nat := 2 ^ 251 - 1

def word (value : Nat) : Expr := .word (Word.ofNatModulo value)
def host (index locals : Nat) (argument : Expr) : Expr :=
  .apply (.var (index + locals)) argument
def gt (left right : Expr) : Expr := .binary .wordGt left right
def add (left right : Expr) : Expr := .binary .wordAdd left right
def sub (left right : Expr) : Expr := .binary .wordSub left right
def mul (left right : Expr) : Expr := .binary .wordMul left right

/-- A complete calldata Word; every read happens after the checks that make
its window present, so the zero branch is unreachable. -/
def readAt (locals : Nat) (address : Expr) : Expr :=
  .caseE (host 8 locals address) (word 0) (.var 0)

/-- One calldata byte, read only once the size admits it. -/
def byteAt (locals offset : Nat) : Expr :=
  .caseE (host 6 locals (word offset)) (word 0) (.var 0)

/-- The first four calldata bytes as a big-endian number. -/
def selectorWord (locals : Nat) : Expr :=
  add (add (add (mul (byteAt locals 0) (word (2 ^ 24))) (mul (byteAt locals 1) (word (2 ^ 16))))
    (mul (byteAt locals 2) (word (2 ^ 8)))) (byteAt locals 3)

/-- A std rejection: revert with the error selector as the Word payload. -/
def reject (error : Nat) : Expr := .inRight .word (.inLeft .word (word error))

/-- std's dispatch and the head of `(uint256 flags, T value)` for a dynamic
`T`: calldata shorter than four bytes or with another selector reaches the
default fallback; a head shorter than 64 bytes, or an offset `o` with
`o > size - 4` or fewer than 32 bytes at `4 + o`, is truncated. The
continuation runs in the frame step, size, flags, offset (positions zero to
three), where the 32-byte Word at `4 + o` exists. -/
def dynamicHead (selector : Nat) (stepBody continuation : Expr) : Expr :=
  .letE stepBody
    (.letE (host 7 1 .unit)
      (.ifE (gt (word 4) (.var 0)) (reject noSelectorError)
        (.ifE (.binary .wordEq (selectorWord 2) (word selector))
          (.ifE (gt (word 68) (.var 0)) (reject truncatedError)
            (.letE (readAt 2 (word 4))
              (.letE (readAt 3 (word 36))
                (.ifE (gt (.var 0) (sub (.var 2) (word 4))) (reject truncatedError)
                  (.ifE (gt (word 32) (sub (.var 2) (add (word 4) (.var 0)))) (reject truncatedError)
                    continuation)))))
          (reject noSelectorError))))

end Solcore.Synthesis.Core.StdDispatch
