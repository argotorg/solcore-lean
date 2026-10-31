import Solcore.Core.Primitive
import Solcore.Core.Wire.Codec.Program

/-! A binder-level builder for de Bruijn Core expressions, shared by the call
profiles' contracts: an expression is built at its binder depth, so a binder's
level names it from inside any later binder. The host functions are the
storage read and write, the input size and the input Word at a byte offset. -/
set_option autoImplicit false

namespace Solcore.Synthesis.Core.CallBuilder

open Solcore.Core (Word)
open Solcore.Core.Wire

private def w (value : Nat) : Word := Word.ofNatModulo value

/-- An expression at a binder depth. -/
abbrev B := Nat → Expr

def bvar (level : Nat) : B := fun depth => .var (depth - 1 - level)
def bword (value : Nat) : B := fun _ => .word (w value)
def bconst (value : Word) : B := fun _ => .word value
def bunit : B := fun _ => .unit
def bhost (index : Nat) (argument : B) : B := fun depth => .apply (.var (index + depth)) (argument depth)
def bapply (function argument : B) : B := fun depth => .apply (function depth) (argument depth)
def blet (value : B) (body : Nat → B) : B := fun depth => .letE (value depth) (body depth (depth + 1))
def bcond (condition yes no : B) : B := fun depth => .ifE (condition depth) (yes depth) (no depth)
def bcase (scrutinee : B) (left right : Nat → B) : B := fun depth =>
  .caseE (scrutinee depth) (left depth (depth + 1)) (right depth (depth + 1))
def bbinary (operator : BinaryOp) (left right : B) : B := fun depth =>
  .binary operator (left depth) (right depth)
def bpair (left right : B) : B := fun depth => .pair (left depth) (right depth)
def binLeft (type : Ty) (value : B) : B := fun depth => .inLeft type (value depth)
def binRight (type : Ty) (value : B) : B := fun depth => .inRight type (value depth)
def bfirst (value : B) : B := fun depth => .first (value depth)
def bsecond (value : B) : B := fun depth => .second (value depth)

def badd (left right : B) : B := bbinary .wordAdd left right
def bsub (left right : B) : B := bbinary .wordSub left right
def bgt (left right : B) : B := bbinary .wordGt left right
def beq (left right : B) : B := bbinary .wordEq left right
def bbitSet (value : B) (bit : Nat) : B := beq (bbinary .wordAnd value (bword bit)) (bword bit)

def sload (slot : Nat) : B := bhost 0 (bword slot)
def sstore (slot : Nat) (value : B) : B := bhost 1 (bpair (bword slot) value)
def inputSize : B := bhost 7 bunit
/-- The input Word at a byte offset; an absent Word reads as zero, which the
checks before every read never reach. -/
def readAt (offset : B) : B := bcase (bhost 8 offset) (fun _ => bword 0) (fun value => bvar value)

/-- Right-nested pairs of the values. -/
def btuple : List B → B
  | [] => bunit
  | [value] => value
  | value :: rest => bpair value (btuple rest)

end Solcore.Synthesis.Core.CallBuilder
