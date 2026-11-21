import Solcore.Frontend.SourceCore.Lowering
import Solcore.SourceSemantics.Dynamic.Primitive
import Solcore.Core.Machine

/-!
# Word opcode tests

The 26 pure word functions of upstream's `std.opcodes` as builtins. The catalog appends them after
the integer helpers and gives them no bare name. Each opcode's Source meaning (`WordOpcode.apply`
and `SourceSemantics.Dynamic.wordOpcodeValue`) and its compiled closure, run on Core's machine, agree with EVM's
rules, computed here on naturals and integers, at the corner cases: zero divisors and moduli,
`sdiv`'s overflow and `smod`'s sign, shifts of 256 or more, `byte` past 31, `signextend` past 30,
`clz(0)`, `exp` past 256 bits, and `addmod` and `mulmod` past 256 bits.
-/

set_option autoImplicit false

namespace Tests.WordOpcodes

open Solcore Solcore.Frontend

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError label)

private def modulus : Nat := 2 ^ 256

/-- A word's signed value, as EVM reads it. -/
private def signed (x : Nat) : Int := if x < 2 ^ 255 then x else (x : Int) - modulus

/-- An integer as a word, modulo 2^256. -/
private def unsigned (x : Int) : Nat := (Int.emod x modulus).toNat

private def bitLength : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, x => if x = 0 then 0 else bitLength fuel (x / 2) + 1

/-- `base ^ exponent` modulo 2^256, by squaring over the exponent's 256 bits. -/
private def powMod (base exponent : Nat) : Nat :=
  ((List.range 256).foldl (fun (state : Nat × Nat × Nat) _ =>
    let (result, square, rest) := state
    (if rest % 2 = 1 then result * square % modulus else result, square * square % modulus, rest / 2))
    (1, base % modulus, exponent)).1

private def flag (holds : Bool) : Nat := if holds then 1 else 0

/-- EVM's rule for each opcode on naturals below 2^256, in EVM's operand order. -/
private def evm : WordOpcode → List Nat → Option Nat
  | .add, [a, b] => some ((a + b) % modulus)
  | .mul, [a, b] => some (a * b % modulus)
  | .sub, [a, b] => some ((a + modulus - b) % modulus)
  | .div, [a, b] => some (if b = 0 then 0 else a / b)
  | .sdiv, [a, b] => some (if b = 0 then 0 else
      let quotient : Int := ((signed a).natAbs / (signed b).natAbs : Nat)
      unsigned (if decide (signed a < 0) == decide (signed b < 0) then quotient else -quotient))
  | .mod, [a, b] => some (if b = 0 then 0 else a % b)
  | .smod, [a, b] => some (if b = 0 then 0 else
      let remainder : Int := ((signed a).natAbs % (signed b).natAbs : Nat)
      unsigned (if signed a < 0 then -remainder else remainder))
  | .addmod, [a, b, n] => some (if n = 0 then 0 else (a + b) % n)
  | .mulmod, [a, b, n] => some (if n = 0 then 0 else a * b % n)
  | .exp, [a, b] => some (powMod a b)
  | .signextend, [b, x] => some (if b ≥ 31 then x else
      let top := 8 * b + 7
      let low := x % 2 ^ (top + 1)
      if x.testBit top then low + (modulus - 2 ^ (top + 1)) else low)
  | .lt, [a, b] => some (flag (decide (a < b)))
  | .gt, [a, b] => some (flag (decide (a > b)))
  | .slt, [a, b] => some (flag (decide (signed a < signed b)))
  | .sgt, [a, b] => some (flag (decide (signed a > signed b)))
  | .eq, [a, b] => some (flag (decide (a = b)))
  | .iszero, [a] => some (flag (decide (a = 0)))
  | .and, [a, b] => some (a &&& b)
  | .or, [a, b] => some (a ||| b)
  | .xor, [a, b] => some (a ^^^ b)
  | .not, [a] => some (modulus - 1 - a)
  | .byte, [i, x] => some (if i ≥ 32 then 0 else x / 2 ^ (248 - 8 * i) % 256)
  | .shl, [s, x] => some (if s ≥ 256 then 0 else x * 2 ^ s % modulus)
  | .shr, [s, x] => some (if s ≥ 256 then 0 else x / 2 ^ s)
  | .sar, [s, x] => some (unsigned (Int.fdiv (signed x) (2 ^ min s 256 : Nat)))
  | .clz, [x] => some (256 - bitLength 257 x)
  | _, _ => none

private def edges : List Nat :=
  [0, 1, 2, 3, 7, 30, 31, 32, 33, 248, 255, 256, 257, 0x1234567890abcdef, 2 ^ 128 + 5,
    2 ^ 255 - 1, 2 ^ 255, 2 ^ 255 + 1, modulus - 2, modulus - 1]

private def ternaryEdges : List Nat :=
  [0, 1, 7, 2 ^ 128 + 1, 2 ^ 200, 2 ^ 255, modulus - 2, modulus - 1]

private def operands (op : WordOpcode) : List (List Nat) :=
  match op.arity with
  | 1 => edges.map ([·])
  | 2 => edges.flatMap fun a => edges.map ([a, ·])
  | _ => ternaryEdges.flatMap fun a => ternaryEdges.flatMap fun b => ternaryEdges.map ([a, b, ·])

/-- The closure's packed argument, as `packArguments` packs the call's words. -/
private def pack : List Core.Word → Core.Expr
  | [] => .unit
  | [word] => .word word
  | word :: rest => .pair (.word word) (pack rest)

private def render (words : List Nat) : String :=
  ", ".intercalate (words.map toString)

/-- Each opcode's meaning and its compiled closure give EVM's word on every corner case. -/
private def testMeanings : IO Nat := do
  let mut cases := 0
  for op in WordOpcode.all do
    for arguments in operands op do
      let words := arguments.map Core.Word.ofNatModulo
      let expected ← match evm op arguments with
        | some expected => pure expected
        | none => throw (IO.userError s!"no EVM rule for {op.name}({render arguments})")
      let label := s!"{op.name}({render arguments}) = {expected}"
      assertTrue ((op.apply words).map (·.val) == some expected) s!"meaning: {label}"
      match SourceSemantics.Dynamic.wordOpcodeValue op (words.map .word) with
      | some (.word word) => assertTrue (word.val == expected) s!"source value {word.val}: {label}"
      | _ => throw (IO.userError s!"source value: {label}")
      match Core.run 64 (.initial (.apply
          (SourceCoreInteger.builtinClosure (.wordOpcode op)) (pack words))) with
      | .done (.inRight .word (.word result)) =>
        assertTrue (result.val == expected) s!"compiled closure gave {result.val}: {label}"
      | other => throw (IO.userError s!"compiled closure: {label}: {reprStr other}")
      cases := cases + 1
  return cases

/-- An opcode on the wrong number of words, or on a value that is no word, has no meaning. -/
private def testOtherArguments : IO Unit := do
  let one := Core.Word.ofNatModulo 1
  for op in WordOpcode.all do
    for count in [0, 1, 2, 3, 4] do
      if count != op.arity then
        assertTrue ((op.apply (List.replicate count one)).isNone)
          s!"{op.name} applied to {count} words"
    let words := List.replicate op.arity (SourceSemantics.Dynamic.Value.word one)
    assertTrue ((SourceSemantics.Dynamic.wordOpcodeValue op (.integer 1 :: words.drop 1)).isNone &&
        (SourceSemantics.Dynamic.wordOpcodeValue op (words.drop 1 ++ [.bool true])).isNone)
      s!"{op.name} applied to a value that is no word"

private def integerHelpers : List BuiltinFunctionId :=
  [.integerSub, .wordFromInteger, .integerAdd, .integerEq, .integerLt, .integerMul, .wordToInteger]

/-- The catalog keeps the integer helpers' places and names and appends the opcodes, which take
their words and give a word, and which no bare name reaches. -/
private def testCatalog : IO Unit := do
  assertTrue (decide (BuiltinFunctionId.all = integerHelpers ++ WordOpcode.all.map .wordOpcode))
    "the catalog is not the integer helpers followed by the opcodes"
  assertTrue (WordOpcode.all.map WordOpcode.name == ["add", "mul", "sub", "div", "sdiv", "mod",
      "smod", "addmod", "mulmod", "exp", "signextend", "lt", "gt", "slt", "sgt", "eq", "iszero",
      "and", "or", "xor", "not", "byte", "shl", "shr", "sar", "clz"])
    "the opcodes' names or order differ from std.opcodes'"
  assertTrue (WordOpcode.all.filter (·.arity == 1) == [.iszero, .not, .clz] &&
      WordOpcode.all.filter (·.arity == 3) == [.addmod, .mulmod] &&
      (WordOpcode.all.filter (·.arity == 2)).length == 21)
    "an opcode takes a number of words other than std.opcodes' function"
  for function in integerHelpers do
    assertTrue (builtinFunctionNamed? function.spelling == some function)
      s!"{function.spelling} lost its bare name"
  for op in WordOpcode.all do
    let function := BuiltinFunctionId.wordOpcode op
    assertTrue (function.spelling == "std.opcodes." ++ op.name) s!"{op.name}'s spelling"
    assertTrue (builtinFunctionNamed? op.name == none &&
        builtinFunctionNamed? function.spelling == none) s!"{op.name} has a bare name"
    assertTrue (function.parameterTypes == List.replicate op.arity .word &&
        function.returnType == .word && function.conversion? == none && function.opcode? == some op)
      s!"{op.name}'s type"

def run : IO Unit := do
  testCatalog
  testOtherArguments
  let cases ← testMeanings
  IO.println s!"word opcodes: catalog, other arguments and {cases} EVM corner cases GREEN"

end Tests.WordOpcodes
