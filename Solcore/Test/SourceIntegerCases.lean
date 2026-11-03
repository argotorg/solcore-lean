import Solcore.Synthesis.Source.CheckedArithmeticCases
import Solcore.Synthesis.Source.ShiftCases

/-! The `runtime-checked-arithmetic` and `runtime-shifts` profiles. Their Core
references compute each operation exactly on Core's integers, range-check or
wrap it, and raise `Panic(code)` or std's `DirtyHigherBitsForInteger()` as
revert data; they agree with the plans' direct interpreter over Lean integers
on generated plans, and four fixtures' sources and results are golden, the
results from the corpus validator's separate Python model. Admission refuses
types, inputs, amounts, helpers, groups and steps outside each profile;
generation draws every shape and replays exactly; tampering is refused, and
reductions are strictly smaller and replay. -/
set_option autoImplicit false

namespace Tests.SourceIntegerCases

open Lean
open Solcore.Core (Word)
open Solcore.Synthesis.Core (Seed)
open Solcore.Synthesis.Core.Integers
open Solcore.Synthesis.Source
open Solcore.Synthesis.Source.Integers (Profile Observed)

private def expect {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fuel : Nat := 1000000

/-- The eight boundary inputs, then four more. -/
private def inputs : List Nat :=
  boundaryWords ++ [3, 7, 2 ^ 128 + 5, 0x1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef]

/-- A returned Word in decimal, revert data in hex. -/
private def observedText : Observed → String
  | .word word => toString word.val
  | .reverted data => Integers.hexBytes data

/-- The reference's outcome at an input. -/
private def referenceText (plan : Plan) (input : Nat) : String :=
  match (plan.applied (Word.ofNatModulo input)).toCore.runStateful fuel with
  | .done value _ => match Observed.ofValue? value with
      | some observed => observedText observed
      | none => "invalid-result"
  | .outOfFuel _ => "out-of-fuel"
  | .fault _ _ => "core-fault"

/-- The interpreter's outcome at an input, as revert data for a revert. -/
private def interpreterText (plan : Plan) : Nat → String := fun input =>
  match plan.outcome input with
  | .word value => toString value
  | .panic code => Integers.hexBytes ([0x4e, 0x48, 0x7b, 0x71] ++ Integers.wordBytes code)
  | .dirty => "0x6cc54a63"

/-! Fixtures. The first checked arithmetic fixture takes an `int8` argument and
returns `int8`: an inline addition, a checked division helper, a block with
`MIN / -1`, a negation, an unchecked multiplication helper and a defaulted
`uint256` literal that wraps, then a lambda with an unchecked body, a compound
remainder and a checked defaulted subtraction. The second is `uint64` over
`run(uint256)`: a compound product, a defaulted addition, a block with a
subtraction from a zero literal, a checked helper and a checked lambda, then a
remainder and a negation. The shift fixtures shift `int16` values by a Word
and a `uint8` amount and by literal amounts in and out of a block, and Words
by `uint256`, `uint16` and `uint128` amounts. -/

private def arithmeticA : Plan := {
  value := .int ⟨true, 1⟩, abi := true, raw := true, inputs := [0, 128, 127], amounts := [],
  helpers := [{op := .mul, unchecked := true}, {op := .div, unchecked := false}],
  groups := [
    {unchecked := false, steps := [.assign (.binary .add (.input 0) (.literal 4)), .assign (.call 1 (.input 1) (.input 2))]},
    {unchecked := true, steps := [.assign (.binary .div (.input 1) (.literal 2)), .assign (.neg (.input 1)),
      .assign (.call 0 (.var 0) (.input 2)), .default {initial := 1, test := .gt 7, chosen := 7, op := .add, operand := 1}]},
    {unchecked := false, steps := [.assign (.apply .sub true (.var 2) (.literal 0)), .assign (.compound .mod (.var 3) (.input 0)),
      .default {initial := 7, test := .bits 1 0, chosen := 0, op := .sub, operand := 1}]}]}

private def arithmeticB : Plan := {
  value := .int ⟨false, 8⟩, abi := false, raw := false, inputs := [0, 1, 2 ^ 64 - 1], amounts := [],
  helpers := [{op := .sub, unchecked := false}],
  groups := [
    {unchecked := false, steps := [.assign (.compound .mul (.input 0) (.input 1)),
      .default {initial := 1, test := .eq 255, chosen := 7, op := .add, operand := 1}]},
    {unchecked := true, steps := [.assign (.binary .sub (.literal 0) (.input 1)), .assign (.call 0 (.literal 7) (.var 1)),
      .assign (.apply .add false (.var 0) (.input 0))]},
    {unchecked := false, steps := [.assign (.binary .mod (.var 2) (.input 2)), .assign (.neg (.var 4))]}]}

private def shiftA : Plan := {
  value := .int ⟨true, 2⟩, abi := false, raw := false, inputs := [0, 2 ^ 15],
  amounts := [{type := .word, offset := 0}, {type := .int ⟨false, 1⟩, offset := 7}], helpers := [],
  groups := [
    {unchecked := false, steps := [.shift {direction := .left, compound := false, value := .input 0, amount := .input 1},
      .shift {direction := .right, compound := false, value := .input 1, amount := .literal 16}]},
    {unchecked := true, steps := [.shift {direction := .left, compound := true, value := .var 0, amount := .input 0},
      .shift {direction := .right, compound := false, value := .literal 0, amount := .input 1}]},
    {unchecked := false, steps := [.shift {direction := .right, compound := true, value := .var 1, amount := .literal 5}]}]}

private def shiftB : Plan := {
  value := .word, abi := false, raw := false, inputs := [0, 3],
  amounts := [{type := .int ⟨false, 32⟩, offset := 255}, {type := .int ⟨false, 2⟩, offset := 256},
    {type := .int ⟨false, 16⟩, offset := 0}], helpers := [],
  groups := [{unchecked := false, steps := [
    .shift {direction := .left, compound := false, value := .input 0, amount := .input 0},
    .shift {direction := .right, compound := false, value := .input 1, amount := .input 1},
    .shift {direction := .right, compound := true, value := .var 0, amount := .input 2},
    .shift {direction := .left, compound := false, value := .literal 7, amount := .literal 14}]}]}


private def arithmeticASource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\nfunction sc_h0(sc_p: int8, sc_q: int8) returns (int8) {\n    unchecked {\n        return (sc_p * sc_q);\n    }\n}\n\nfunction sc_h1(sc_p: int8, sc_q: int8) returns (int8) {\n    return (sc_p / sc_q);\n}\n\nfunction sc_apply(sc_f: function (int8) returns (int8), sc_v: int8) returns (int8) {\n    return sc_f(sc_v);\n}\n\ncontract SynthesizedCheckedArithmetic {\n    function run(input: int8) public returns (int8) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: int8 = input;\n        let sc_a1: int8 = Typedef.abs(sc_signextend(0, (sc_x + 128)));\n        let sc_a2: int8 = Typedef.abs(sc_signextend(0, (sc_x + 127)));\n        let sc_acc: word = 0;\n        let sc_v0: int8 = (sc_a0 + 1);\n        let sc_v1: int8 = sc_h1(sc_a1, sc_a2);\n        let sc_v2: int8 = 0;\n        let sc_v3: int8 = 0;\n        let sc_v4: int8 = 0;\n        let sc_d0 = 1;\n        if (sc_x > 7) {\n            sc_d0 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        }\n        let sc_e0 = 0;\n        unchecked {\n            sc_v2 = (sc_a1 / (-1));\n            sc_v3 = (-sc_a1);\n            sc_v4 = sc_h0(sc_v0, sc_a2);\n            sc_e0 = (sc_d0 + 1);\n        }\n        let sc_d1 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        if ((sc_x & 1) == 0) {\n            sc_d1 = 0;\n        }\n        let sc_v5: int8 = sc_apply(lam (sc_l: int8) -> int8 {\n            unchecked {\n                return (sc_l - (-128));\n            }\n        }, sc_v2);\n        let sc_v6: int8 = sc_v3;\n        sc_v6 %= sc_a0;\n        let sc_e1 = (sc_d1 - 1);\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v5));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v6));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e1));\n        return Typedef.abs(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def arithmeticAResults : List String := [
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "115792089237316195423570985008687907853269984665640564039457584007913129639831",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x6cc54a63",
    "0x6cc54a63",
    "34",
    "0x6cc54a63",
    "0x6cc54a63",
    "115792089237316195423570985008687907853269984665640564039457584007913129639845",
    "115792089237316195423570985008687907853269984665640564039457584007913129639885",
    "0x6cc54a63",
    "0x6cc54a63"]

private def arithmeticBSource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.unchecked.unsigned;\nimport * from std.dispatch;\n\nfunction sc_h0(sc_p: uint64, sc_q: uint64) returns (uint64) {\n    return (sc_p - sc_q);\n}\n\nfunction sc_apply(sc_f: function (uint64) returns (uint64), sc_v: uint64) returns (uint64) {\n    return sc_f(sc_v);\n}\n\ncontract SynthesizedCheckedArithmetic {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: uint64 = Typedef.abs((sc_x & 0xffffffffffffffff));\n        let sc_a1: uint64 = Typedef.abs(((sc_x + 1) & 0xffffffffffffffff));\n        let sc_a2: uint64 = Typedef.abs(((sc_x + 18446744073709551615) & 0xffffffffffffffff));\n        let sc_acc: word = 0;\n        let sc_d0 = 1;\n        if (sc_x == 255) {\n            sc_d0 = 115792089237316195423570985008687907853269984665640564039457584007913129639935;\n        }\n        let sc_v0: uint64 = sc_a0;\n        sc_v0 *= sc_a1;\n        let sc_e0 = (sc_d0 + 1);\n        let sc_v1: uint64 = 0;\n        let sc_v2: uint64 = 0;\n        let sc_v3: uint64 = 0;\n        unchecked {\n            sc_v1 = (0 - sc_a1);\n            sc_v2 = sc_h0(18446744073709551615, sc_v1);\n            sc_v3 = sc_apply(lam (sc_l: uint64) -> uint64 {\n                return (sc_l + sc_a0);\n            }, sc_v0);\n        }\n        let sc_v4: uint64 = (sc_v2 % sc_a2);\n        let sc_v5: uint64 = (-sc_v4);\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_e0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v5));\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def arithmeticBResults : List String := [
    "26959943495939220800718331828086778140708015150586758381788765843113",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000012",
    "10601109357008446254964315403763482149948774975692891568105106563444499231",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "26959943495939220800718331828086778140708015150586758381788765843113",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011",
    "0x4e487b710000000000000000000000000000000000000000000000000000000000000011"]

private def shiftASource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.signed;\nimport * from std.unchecked.signed;\nimport * from std.dispatch;\nimport { signextend as sc_signextend } from std.opcodes;\n\ncontract SynthesizedShifts {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: int16 = Typedef.abs(sc_signextend(1, sc_x));\n        let sc_a1: int16 = Typedef.abs(sc_signextend(1, (sc_x + 32768)));\n        let sc_k0: word = sc_x;\n        let sc_k1: uint8 = Typedef.abs(((sc_x + 7) & 0xff));\n        let sc_acc: word = 0;\n        let sc_v0: int16 = (sc_a0 << sc_k1);\n        let sc_v1: int16 = (sc_a1 >> 300);\n        let sc_v2: int16 = 0;\n        let sc_v3: int16 = 0;\n        unchecked {\n            sc_v2 = sc_v0;\n            sc_v2 <<= sc_k0;\n            sc_v3 = ((-32768) >> sc_k1);\n        }\n        let sc_v4: int16 = sc_v1;\n        sc_v4 >>= 15;\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v0));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v1));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v2));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v3));\n        sc_acc = ((sc_acc * 1099511628211) ^ Typedef.rep(sc_v4));\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def shiftAResults : List String := [
    "115792089237316195423570985008687907853268655437643201475389458753201454373290",
    "115792089237316195423570984634543488104466189583693770850429139307045459162154",
    "115792089237316195423570983512110228858058792021838051335306591137569476660202",
    "115792089237316195423570961156981148867111457248327539795385640839944169645162",
    "47890485727846714300077608985593429736312073170672042",
    "93536104937200616463487512398745113151610115063232",
    "115792089237316195423570985008687907853268655437643201475389458753201454373290",
    "93536104937200616463487512398745113151610115063232",
    "115792089237316195423570980518954870867639065190272316896590392323894338944394",
    "23945242863923356485424805811514680805719995771011412",
    "115792089237316195423570955077134327949071387121639233876953295458678879201058",
    "115792089237316195423570985008687907853269984665640564039457584006813618011725"]

private def shiftBSource : String :=
  "import * from std;\nimport * from std.unsigned;\nimport * from std.dispatch;\n\ncontract SynthesizedShifts {\n    function run(input: uint256) public returns (uint256) {\n        let sc_x: word = Typedef.rep(input);\n        let sc_a0: word = sc_x;\n        let sc_a1: word = (sc_x + 3);\n        let sc_k0: uint256 = Typedef.abs((sc_x + 255));\n        let sc_k1: uint16 = Typedef.abs(((sc_x + 256) & 0xffff));\n        let sc_k2: uint128 = Typedef.abs((sc_x & 0xffffffffffffffffffffffffffffffff));\n        let sc_acc: word = 0;\n        let sc_v0: word = (sc_a0 << sc_k0);\n        let sc_v1: word = (sc_a1 >> sc_k1);\n        let sc_v2: word = sc_v0;\n        sc_v2 >>= sc_k2;\n        let sc_v3: word = (115792089237316195423570985008687907853269984665640564039457584007913129639935 << 256);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v0);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v1);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v2);\n        sc_acc = ((sc_acc * 1099511628211) ^ sc_v3);\n        return uint256(sc_acc);\n    }\n}\n"

/-- From the Python model of `Tests/scripts/test-semantic-checked-arithmetic-corpus.py`. -/
private def shiftBResults : List String := [
    "0",
    "0",
    "0",
    "0",
    "0",
    "28948022309329048855892746252171976963317496166410141009864396001978282409984",
    "0",
    "1208925820571204291060521",
    "0",
    "0",
    "0",
    "0"]

private def fixtures : List (String × Profile × Plan × String × List String) := [
  ("arithmeticA", CheckedArithmetic.profile, arithmeticA, arithmeticASource, arithmeticAResults),
  ("arithmeticB", CheckedArithmetic.profile, arithmeticB, arithmeticBSource, arithmeticBResults),
  ("shiftA", Shifts.profile, shiftA, shiftASource, shiftAResults),
  ("shiftB", Shifts.profile, shiftB, shiftBSource, shiftBResults)]

private def fixtureChecks : IO Unit := do
  for (name, profile, plan, source, results) in fixtures do
    ensure (profile.admitted plan) (name ++ " is not admitted")
    ensure (plan.applied Word.zero).check (name ++ " failed the Core checker")
    ensure ((profile.emit plan).source == source) (name ++ " source differs from its golden text")
    ensure (results.length == inputs.length) (name ++ " golden results are incomplete")
    for (input, expected) in inputs.zip results do
      ensure (referenceText plan input == expected) s!"{name} reference differs at {input}"
      ensure (interpreterText plan input == expected) s!"{name} interpreter differs at {input}"
  let texts := fixtures.flatMap fun (_, _, _, _, results) => results
  for expected in ["0x6cc54a63", "0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ "11",
      "0x4e487b71" ++ String.ofList (List.replicate 62 '0') ++ "12"] do
    ensure (texts.contains expected) ("the fixtures reach no " ++ expected)

/-! Admission. -/

private def binary : Step := .assign (.binary .add (.input 0) (.input 0))
private def shiftStep : Step := .shift {direction := .left, compound := false, value := .input 0, amount := .literal 1}
private def defaulted : Step := .default {initial := 0, test := .eq 0, chosen := 1, op := .add, operand := 1}
private def checked (steps : List Step) : List Group := [{unchecked := false, steps}]

private def arithmeticRefusals : List (String × Plan) :=
  let base : Plan := {
    value := .int ⟨false, 1⟩, abi := false, raw := false, inputs := [0], amounts := [],
    helpers := [], groups := checked [binary]}
  [("a Word type", {base with value := .word}), ("a 24-bit type", {base with value := .int ⟨false, 3⟩}),
    ("no input", {base with inputs := []}), ("four inputs", {base with inputs := [0, 1, 3, 1]}),
    ("a first offset", {base with inputs := [1]}), ("an offset outside the table", {base with inputs := [0, 2]}),
    ("an amount", {base with amounts := [{type := .word, offset := 0}]}),
    ("three helpers", {base with
      helpers := List.replicate 3 {op := .add, unchecked := false}
      groups := checked [.assign (.call 0 (.input 0) (.input 0)), .assign (.call 1 (.input 0) (.input 0)),
        .assign (.call 2 (.input 0) (.input 0))]}),
    ("a helper nothing calls", {base with helpers := [{op := .add, unchecked := false}]}),
    ("a call past the helpers", {base with groups := checked [.assign (.call 0 (.input 0) (.input 0))]}),
    ("a 256-bit T result", {base with value := .int ⟨false, 32⟩, raw := true}),
    ("no group", {base with groups := []}), ("an empty group", {base with groups := checked []}),
    ("adjacent blocks", {base with groups := [{unchecked := true, steps := [binary]}, {unchecked := true, steps := [binary]}]}),
    ("four blocks", {base with groups := (List.range 7).map fun index => {unchecked := index % 2 == 0, steps := [binary]}}),
    ("eleven steps", {base with groups := checked (List.replicate 11 binary)}),
    ("a variable before it exists", {base with groups := checked [.assign (.binary .add (.var 0) (.input 0))]}),
    ("an input past the inputs", {base with groups := checked [.assign (.binary .add (.input 1) (.input 0))]}),
    ("a literal past the table", {base with groups := checked [.assign (.binary .add (.input 0) (.literal 8))]}),
    ("a negated literal", {base with groups := checked [.assign (.neg (.literal 0))]}),
    ("a lambda block inside a block",
      {base with groups := [{unchecked := true, steps := [.assign (.apply .add true (.input 0) (.input 0))]}]}),
    ("only defaulted results", {base with groups := checked [defaulted]}),
    ("three defaulted results", {base with groups := checked [binary, defaulted, defaulted, defaulted]}),
    ("a defaulted literal past the table", {base with groups := checked [binary,
      .default {initial := 8, test := .eq 0, chosen := 1, op := .add, operand := 1}]}),
    ("a test constant outside the table", {base with groups := checked [binary,
      .default {initial := 0, test := .eq 3, chosen := 1, op := .add, operand := 1}]}),
    ("a mask outside the table", {base with groups := checked [binary,
      .default {initial := 0, test := .bits 2 0, chosen := 1, op := .add, operand := 1}]}),
    ("a bit value above its mask", {base with groups := checked [binary,
      .default {initial := 0, test := .bits 1 2, chosen := 1, op := .add, operand := 1}]}),
    ("a shift", {base with groups := checked [shiftStep]})]

private def arithmeticControls : List Plan :=
  let base : Plan := {
    value := .int ⟨true, 32⟩, abi := true, raw := false, inputs := [0, 2 ^ 255 - 1, 2 ^ 256 - 1],
    amounts := [], helpers := [{op := .div, unchecked := true}, {op := .mod, unchecked := false}],
    groups := [{unchecked := true, steps := [.assign (.call 0 (.input 2) (.literal 10)), defaulted]},
      {unchecked := false, steps := [.assign (.call 1 (.var 0) (.input 1)), defaulted]}, {unchecked := true, steps := [binary]},
      {unchecked := false, steps := [binary]}, {unchecked := true, steps := [.assign (.neg (.var 1))]}]}
  [base, {base with
    value := .int ⟨false, 1⟩, inputs := [0, 1, 255], raw := true, abi := false
    groups := checked (List.replicate 10 binary), helpers := []},
    {base with groups := [{unchecked := false, steps := [.assign (.apply .mod true (.input 0) (.literal 10)),
      .assign (.call 0 (.input 0) (.input 0)), .assign (.call 1 (.var 1) (.var 0))]}]}]

private def shiftRefusals : List (String × Plan) :=
  let base : Plan := {
    value := .word, abi := false, raw := false, inputs := [0], amounts := [{type := .word, offset := 0}],
    helpers := [], groups := checked [shiftStep]}
  [("run(T)", {base with abi := true}), ("a T result", {base with value := .int ⟨true, 1⟩, raw := true}),
    ("no amount", {base with amounts := []}),
    ("four amounts", {base with amounts := List.replicate 4 {type := .word, offset := 0}}),
    ("a signed amount", {base with amounts := [{type := .int ⟨true, 1⟩, offset := 0}]}),
    ("an amount offset outside the table", {base with amounts := [{type := .word, offset := 2}]}),
    ("an amount past the amounts", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .input 0, amount := .input 1}]}),
    ("an amount literal past the table", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .input 0, amount := .literal 17}]}),
    ("a helper", {base with helpers := [{op := .add, unchecked := false}]}),
    ("an operation", {base with groups := checked [binary]}),
    ("a defaulted result", {base with groups := checked [shiftStep, defaulted]}),
    ("a value past the literals", {base with
      groups := checked [.shift {direction := .left, compound := false, value := .literal 8, amount := .literal 1}]})]

private def shiftControls : List Plan :=
  let base : Plan := {
    value := .int ⟨true, 16⟩, abi := false, raw := false, inputs := [0, 1, 2 ^ 128 - 1],
    amounts := [{type := .int ⟨false, 32⟩, offset := 300}, {type := .int ⟨false, 1⟩, offset := 255}, {type := .word, offset := 0}],
    helpers := [], groups := [{unchecked := true, steps := List.replicate 4 shiftStep},
      {unchecked := false, steps := List.replicate 6 shiftStep}]}
  [base, {base with value := .word, inputs := [0], amounts := [{type := .int ⟨false, 2⟩, offset := 0}]}]

private def admissionChecks : IO Unit := do
  for (label, plan) in arithmeticRefusals do
    ensure (!plan.arithmeticAdmitted) ("checked arithmetic admission accepted " ++ label)
  for (label, plan) in shiftRefusals do
    ensure (!plan.shiftAdmitted) ("shift admission accepted " ++ label)
  for plan in arithmeticControls do
    ensure plan.arithmeticAdmitted ("checked arithmetic admission refused a control: " ++ reprStr plan)
    ensure (!plan.shiftAdmitted) "shift admission accepted a checked arithmetic plan"
  for plan in shiftControls do
    ensure plan.shiftAdmitted ("shift admission refused a control: " ++ reprStr plan)
    ensure (!plan.arithmeticAdmitted) "checked arithmetic admission accepted a shift plan"

/-! The reference against the interpreter. -/

private def modelChecks : IO Unit := do
  let mut outcomes := 0
  let mut reverts := 0
  let mut panics : List String := []
  for (generate, admitted) in [(generateArithmetic, Plan.arithmeticAdmitted), (generateShifts, Plan.shiftAdmitted)] do
    for seed in List.range 200 do
      let plan := (generate (UInt64.ofNat seed)).fit Integers.defaultNodes
      ensure (admitted plan) s!"seed {seed} drew a plan outside its profile"
      ensure (plan.applied Word.zero).check s!"seed {seed} failed the Core checker"
      for input in inputs do
        let expected := interpreterText plan input
        ensure (referenceText plan input == expected) s!"seed {seed}: reference and interpreter differ at {input}"
        outcomes := outcomes + 1
        if expected.startsWith "0x" then
          reverts := reverts + 1
          unless panics.contains expected do panics := panics ++ [expected]
  ensure (outcomes == 4800) "the model checks lost outcomes"
  ensure (reverts > 1000 && panics.length == 3) s!"the model checks reached {reverts} reverts of {panics.length} kinds"

/-! Generation and replay. -/

private def shapeValues (shapes : List (String × List String)) : List (String × String) :=
  shapes.flatMap fun (dimension, values) => values.map (dimension, ·)

private def generationChecks : IO Unit := do
  for (profile, count, recorded) in [(CheckedArithmetic.profile, 1000, ["typeOutcomes"]), (Shifts.profile, 300, [])] do
    let mut seen : List (String × String) := []
    for seed in List.range count do
      let plan := (profile.generate (UInt64.ofNat seed)).fit Integers.defaultNodes
      ensure (plan == (profile.generate (UInt64.ofNat seed)).fit Integers.defaultNodes) "generation is not deterministic"
      for value in shapeValues (profile.shapes plan) do
        unless seen.contains value do seen := seen ++ [value]
    let all := shapeValues (if profile.label == "shift" then shiftShapeInventory else arithmeticShapeInventory)
    for value in seen do
      ensure (all.contains value) s!"{profile.label}: {value.1} {value.2} is outside the inventory"
    for value in all do
      unless recorded.contains value.1 do
        ensure (seen.contains value) s!"{profile.label}: {value.1} {value.2} is never drawn"
    let corpus := profile.generateCases (Seed.ofNat 1) Integers.defaultNodes 64 400 fuel
    let cases ← expect (corpus.getObjValAs? (Array Json) "cases")
    ensure (cases.size == 64) (profile.label ++ ": generation did not complete 64 cases")
    for case in cases do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a generated case does not replay")
    let seeded := profile.generateCases (Seed.ofNat 7) Integers.defaultNodes 24 400 fuel .seeded .nonIdentity
    for case in ← expect (seeded.getObjValAs? (Array Json) "cases") do
      ensure ((profile.replayCase case fuel).toOption == some case) (profile.label ++ ": a seeded case does not replay")
    let small := (List.range 200).any fun seed =>
      ((profile.generate (UInt64.ofNat seed)).fit 256).stepCount < (profile.generate (UInt64.ofNat seed)).stepCount
    ensure small (profile.label ++ ": a 256-node budget never drops a step")

/-! Tampering and reduction. -/

private def setObj (json : Json) (key : String) (value : Json) : Json :=
  match json with
  | .obj fields => .obj (fields.insert key value)
  | other => other

private def tamperChecks : IO Unit := do
  for (name, profile, plan, _, _) in fixtures do
    let some checkedPlan := Integers.CheckedPlan.ofPlan? (profile := profile) plan | throw (IO.userError name)
    let case ← expect (profile.emitCase checkedPlan (Word.ofNatModulo 2) (Json.mkObj [("kind", toJson "imported")]) fuel)
    ensure ((profile.replayCase case fuel).toOption == some case) (name ++ " does not replay")
    let source ← expect (case.getObjValAs? String "source")
    let provenance ← expect (case.getObjVal? "provenance")
    let contract ← expect (case.getObjVal? "contract")
    for (label, tampered) in [
        ("source", setObj case "source" (toJson (source ++ "\n"))),
        ("input", setObj case "input" (toJson "3")),
        ("program", setObj case "program" (Json.mkObj [])),
        ("plan", setObj case profile.planKey (profile.planJson {plan with raw := !plan.raw})),
        ("shapes", setObj case "provenance" (setObj provenance profile.shapesKey (Json.mkObj []))),
        ("generator version", setObj case "provenance" (setObj provenance "generatorVersion" (toJson "core-halt-v1"))),
        ("wrapper", setObj case "contract" (setObj contract "name" (toJson "SynthesizedRevertData")))] do
      ensure (profile.replayCase tampered fuel).toOption.isNone (name ++ ": replay accepted an altered " ++ label)
    let forged := setObj case "directCore" (Json.mkObj [("stage", toJson "execution"), ("status", toJson "returned"),
      ("word", toJson "7")])
    ensure ((profile.replayCase forged fuel).toOption == some case) (name ++ ": replay trusted the saved observation")
    let shrunk ← expect (profile.shrinkCases case 64 fuel)
    let candidates ← expect (shrunk.getObjValAs? (Array Json) "cases")
    ensure (candidates.size ≥ 8) (name ++ " has too few reductions")
    for candidate in candidates do
      ensure ((profile.replayCase candidate fuel).toOption == some candidate) (name ++ ": a reduction does not replay")
  let some source := Integers.CheckedPlan.ofPlan? (profile := CheckedArithmetic.profile) arithmeticA | throw (IO.userError "A")
  let reduced := (Integers.reductions ⟨source, Word.ofNatModulo 2⟩).map (·.candidate.plan.plan)
  for (label, expected) in [("run(uint256)", {arithmeticA with abi := false}), ("a uint256 result", {arithmeticA with raw := false})] do
    ensure (reduced.contains expected) ("no reduction to " ++ label)
  let blocked (plan : Plan) : Nat := (plan.steps.filter (·.1)).length
  ensure (reduced.any fun plan => blocked plan < blocked arithmeticA) "no reduction moves a step out of its block"
  ensure (reduced.any fun plan => plan.inputs.length < arithmeticA.inputs.length) "no reduction removes an input"
  ensure (reduced.any fun plan => plan.helpers.any (·.unchecked) != arithmeticA.helpers.any (·.unchecked))
    "no reduction checks a helper"

def testSourceIntegerCases : IO Unit := do
  fixtureChecks
  admissionChecks
  modelChecks
  generationChecks
  tamperChecks

end Tests.SourceIntegerCases
