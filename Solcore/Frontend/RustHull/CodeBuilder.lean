import Solcore.Frontend.RustHull.LoweringSupport
import Solcore.Core.WordMapping

/-! Lexical Core expression builders for the imported contract runtime. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.CodeBuilder
open Core
abbrev Code := Nat → Core.Expr
def constant (value : Core.Expr) : Code := fun _ => value
def number (value : Nat) : Code := constant (.word (Word.ofNatModulo value))
def boolean (value : Bool) : Code := constant (.bool value)
def unit : Code := constant .unit
def empty : Code := constant WordMapping.empty
def part (index count : Nat) (value : Code) : Code :=
  fun depth => projectArgument index count (value depth)
def packet (values : List Code) : Code := fun depth => bundle (values.map (· depth))
def bind (value : Code) (body : Code → Code) : Code := fun depth =>
  .letE (value depth) (body (fun here => .var (here - depth - 1)) (depth + 1))
def bindResult (type : Core.Ty) (value : Code) (body : Code → Code) : Code := fun depth =>
  LanguageResult.bind type (value depth)
    (body (fun here => .var (here - depth - 1)) (depth + 1))
def success (value : Code) : Code := fun depth => LanguageResult.success (value depth)
def failure (type : Core.Ty) (reason : Code) : Code := fun depth => LanguageResult.failure type (reason depth)
def lambda (parameter result : Core.Ty) (body : Code → Code) : Code := fun depth =>
  .lambda parameter result (body (fun here => .var (here - depth - 1)) (depth + 1))
def apply (function argument : Code) : Code := fun depth => .apply (function depth) (argument depth)
def choose (test yes no : Code) : Code := fun depth => .ifE (test depth) (yes depth) (no depth)
def binary (op : BinaryOp) (a b : Code) : Code := fun depth => .binary op (a depth) (b depth)
def load (reference : Code) : Code := fun depth => .loadCell (reference depth)
def store (reference value : Code) : Code := fun depth => .storeCell (reference depth) (value depth)
def allocate (type : Core.Ty) (value : Code) : Code := fun depth => .newCell type (value depth)
def present (value : Code) : Code := fun depth => .inRight .unit (value depth)
def lookup (mapping key : Code) : Code := fun depth => WordMapping.lookup (mapping depth) (key depth)
def insert (mapping key value : Code) : Code := fun depth =>
  WordMapping.insert (mapping depth) (key depth) (value depth)
def address (value : Code) : Code := binary .wordAnd value (number (2 ^ 160 - 1))
end Solcore.Frontend.RustHull.CodeBuilder
